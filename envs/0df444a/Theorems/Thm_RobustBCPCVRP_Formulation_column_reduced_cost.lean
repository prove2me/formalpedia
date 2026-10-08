-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_column_reduced_cost
-- name    : RobustBCPCVRP.Formulation.column_reduced_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:56.051848+00:00
-- url     : https://prove2.me/theorems/431a02cd-d107-4192-9d01-11f0848dbd2f
-- title:
--   §3.1, p. 6 — the reduced cost of a column is the sum of the edge reduced costs c̄ₑ along its q-route
-- statement:
--   Let $G=(V,E)$ be a graph without loops, $\ell$ edge lengths, and take arbitrary dual values: $\mu_i$ for (8), $\nu$ for (9), $\pi_S$ for (10) ($S\subseteq V_+$), $\omega_e$ for (11), and $\alpha_t$ for finitely many generic cuts $\sum_j(\sum_e a_{t,e}q^e_j)\lambda_j\ge b_t$. Let $r$ be a q-route without 2-cycles with edge incidences $q^e=q^e(r)$. Then the reduced cost of the column of $r$ in the DWM — its cost coefficient minus the duals times its coefficients in the rows (8)–(11) and in the cuts —
--   $$\sum_{e\in E}\ell_eq^e-\sum_{i\in V_+}\mu_i\sum_{e\in\delta(\{i\})}q^e-\nu\sum_{e\in\delta(\{0\})}q^e-\sum_{S\subseteq V_+}\pi_S\sum_{e\in\delta(S)}q^e-\sum_{e\in E\setminus\delta(\{0\})}\omega_eq^e-\sum_t\alpha_t\sum_{e\in E}a_{t,e}q^e$$
--   equals
--   $$\sum_{e\in E}\bar c_e\,q^e ,$$
--   where $\bar c_e$ is the edge reduced cost of the paper (with the term $-a_{t,e}\alpha_t$ of each generic cut).
--
--   This is what lets the pricing problem be solved as a shortest q-route problem on the graph with edge costs $\bar c_e$, independently of how many cuts are in the master.
--
--   **Formalization Note** The identity holds for every dual vector; no dual feasibility or sign condition is assumed. The loop-free hypothesis on $G$ is needed because a loop at a client would enter $\bar c_e$ but no cut value.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 6, §3.1, display of c̄ₑ and the paragraph after it

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem column_reduced_cost {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (C : ℕ) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    {ι : Type*} [Fintype ι] (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (μ : Fin (n + 1) → ℝ) (ν : ℝ) (π : Finset (Fin (n + 1)) → ℝ)
    (ω : Sym2 (Fin (n + 1)) → ℝ) (a : ι → Sym2 (Fin (n + 1)) → ℝ) (α : ι → ℝ)
    (r : List (Fin (n + 1))) (hr : IsQRoute E d C r) :
    ∑ e ∈ E, ℓ e * (inc r e : ℝ)
        - ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0), μ i * cutCoeff r {i}
        - ν * cutCoeff r {0}
        - ∑ S ∈ clientSets n, π S * cutCoeff r S
        - ∑ e ∈ E.filter (fun e => (0 : Fin (n + 1)) ∉ e), ω e * (inc r e : ℝ)
        - ∑ t, α t * ∑ e ∈ E, a t e * (inc r e : ℝ)
      = ∑ e ∈ E, edgeReducedCost ℓ μ ν π ω a α e * (inc r e : ℝ) := by sorry
end RobustBCPCVRP.Formulation
