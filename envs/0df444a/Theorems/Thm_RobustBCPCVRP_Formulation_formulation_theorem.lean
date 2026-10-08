-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_formulation_theorem
-- name    : RobustBCPCVRP.Formulation.formulation_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:04.773632+00:00
-- url     : https://prove2.me/theorems/52682730-829a-4c51-966d-8aa1c357fd96
-- title:
--   §2, pp. 4–5 — integer points of P₃ = P₁ ∩ P₂ are exactly the CVRP solutions; P₃ is the DWM image; L₁, L₂ ≤ L₃ ≤ OPT
-- statement:
--   Let $G=(V,E)$ be a graph without loops on $V=\{0,1,\dots,n\}$ (depot $0$, clients $V_+$), with positive client demands $d_i>0$, $K>0$ vehicles of positive capacity $C>0$, and arbitrary edge lengths $\ell$. Let $P_1$, $P_2$ be the polytopes of the paper, $P_3$ the Explicit Master (constraints (1)–(6) with one vector $\lambda\ge 0$ of weights on q-routes without 2-cycles), and DWM the Dantzig–Wolfe Master (7)–(11). Then:
--
--   1. **(exactness)** a vector $x$ is an integer point of $P_3$ if and only if $x=\chi(R)$ is the edge vector of some feasible CVRP solution $R=(R_1,\dots,R_K)$;
--   2. **(the DWM describes $P_3$)** $x\in P_3$ if and only if $x=Q\lambda$ for some $\lambda$ feasible for (8)–(11), and for every family of columns $\lambda$
--   $$\sum_j\sum_{e\in E}\ell_eq^e_j\lambda_j=\sum_{e\in E}\ell_e(Q\lambda)_e ;$$
--   3. **(bounds)** writing $L_i=\min_{x\in P_i}\sum_{e\in E}\ell_ex_e$ and OPT for the CVRP optimum,
--   $$L_1\le L_3,\qquad L_2\le L_3,\qquad L_3\le\mathrm{OPT},$$
--   in the form: every lower bound on $\ell^\top x$ over $P_1$ (or over $P_2$) is a lower bound over $P_3$, and every lower bound over $P_3$ is at most the cost of every feasible CVRP solution.
--
--   This is the formulation the paper's branch-and-cut-and-price is built on: optimizing over the intersection of the capacity-cut polytope and the q-route polytope gives a valid relaxation whose integer points are exactly the solutions, it can be solved by column generation on the DWM, and its bound dominates both classical bounds.
--
--   **Formalization Note** The minima $L_1,L_2,L_3$ and OPT are not taken as real infima: $P_3$ is empty when the instance is infeasible, and a real infimum of the empty set would be $0$. Each inequality is stated for every lower bound $L$ instead. The vector $x$ is a function on unordered vertex pairs vanishing off $E$, and the q-route weights $\lambda$ range over all finitely supported families on q-routes without 2-cycles. Positive demands, a positive number of vehicles $K>0$, positive capacity and a loop-free graph are standing assumptions of the paper (p. 1) and are carried as hypotheses; nonnegative lengths $\ell\ge 0$ are also a standing assumption but no part of the statement uses them, so $\ell$ is arbitrary.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 1 (abstract), pp. 4–5, §2, P₁ (1)–(4), P₂ (5)–(6), P₃, L₁, L₂, L₃, DWM (7)–(11)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem formulation_theorem {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ i : Fin (n + 1), i ≠ 0 → 0 < d i) (hK : 0 < K) (hC : 0 < C) :
    -- (i) the integer points of P₃ are exactly the edge vectors of the CVRP solutions
    (∀ x : Sym2 (Fin (n + 1)) → ℝ, (InP3 E d K C x ∧ IsIntegerVec x) ↔
      ∃ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R ∧ x = chi R) ∧
    -- (ii) P₃ is the image x = Qλ of the DWM-feasible λ, and (7) is ℓᵀ(Qλ)
    (∀ x : Sym2 (Fin (n + 1)) → ℝ, InP3 E d K C x ↔
      ∃ lam : List (Fin (n + 1)) →₀ ℝ, IsDWMFeasible E d K C lam ∧ x = colSum lam) ∧
    (∀ lam : List (Fin (n + 1)) →₀ ℝ, IsColumns E d C lam →
      dwmObjective E ℓ lam = ∑ e ∈ E, ℓ e * colSum lam e) ∧
    -- (iii) L₁ ≤ L₃, L₂ ≤ L₃ and L₃ ≤ OPT, in lower-bound form
    (∀ L : ℝ, (∀ x, InP1 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) ∧
    (∀ L : ℝ, (∀ x, InP2 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) ∧
    (∀ L : ℝ, (∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R → L ≤ cost ℓ R) := by sorry
end RobustBCPCVRP.Formulation
