-- Prove2me | Theorems.Thm_VBSDP_Duality_Supplement_theorem_5_3_star
-- name    : VBSDP.Duality.Supplement.theorem_5_3_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:11:55.751309+00:00
-- url     : https://prove2.me/theorems/b2317e66-f96a-4387-bb12-15fcd1612c14
-- title:
--   Theorem 5.3* — potential reduction method 2* lowers φ by at least 0.05 per iteration
-- statement:
--   Consider the semidefinite program: minimize $c^Tx$ subject to $F(x)=F_0+\sum_{i=1}^mx_iF_i\succeq0$, with data $c\in\mathbb R^m$ and symmetric $F_0,\dots,F_m\in\mathbb R^{n\times n}$, $n\ge1$, and its dual (27): maximize $-\operatorname{Tr}F_0Z$ subject to $Z=Z^T\succeq0$, $\operatorname{Tr}F_iZ=c_i$. Assume that $F_1,\dots,F_m$ are linearly independent. Fix $\nu\ge1$ and the potential
--
--   $$\varphi(x,Z)=\nu\sqrt n\,\log\operatorname{Tr}F(x)Z-\log\det F(x)Z+n\log\operatorname{Tr}F(x)Z-n\log n.$$
--
--   Let $(x,Z)$ be strictly feasible, i.e. $F(x)\succ0$, $Z\succ0$ and $\operatorname{Tr}F_iZ=c_i$ for all $i$. Let $(\delta x^d,\delta Z^d)$ be a solution of the dual system (66) at $(x,Z)$, with $\rho=(n+\nu\sqrt n)/(c^Tx+\operatorname{Tr}F_0Z)$:
--
--   $$Z^{-1}\delta Z^dZ^{-1}+\sum_i\delta x^d_iF_i=-\rho F(x)+Z^{-1},\qquad\operatorname{Tr}F_j\delta Z^d=0,$$
--
--   and let $p,q\in\mathbb R$ minimize $\varphi(x+p\,\delta x^d,\,Z+q\,\delta Z^d)$ over all real step lengths for which the new pair is strictly feasible. Then
--
--   $$\varphi(x+p\,\delta x^d,\;Z+q\,\delta Z^d)\le\varphi(x,Z)-0.05.$$
--
--   Equivalently, if $x^{(k)},Z^{(k)}$ are the iterates of potential reduction method 2* (the algorithm of p. 77 with the directions $\delta x^d,\delta Z^d$), then $\varphi(x^{(k+1)},Z^{(k+1)})\le\varphi(x^{(k)},Z^{(k)})-0.05$ for every executed iteration. Combined with Theorem 5.1 this gives the method a polynomial worst-case iteration bound.
--
--   **Formalization Note** The theorem is stated for one arbitrary iteration: every iteration of the algorithm starts from a strictly feasible pair, and the stopping rule (duality gap $\le\epsilon$) only decides whether the step is taken, so the one-step statement covers every iteration of every run. $\varphi$ is the published `VBSDP.Potential.phi` (the first line of (55)), $(66)$ is `IsDualSearchDirection`, and the exact plane search is `IsPlaneSearchMinimizer`. "$\ge0$"/"$>0$" for matrices mean positive semidefinite/definite (`PosSemidef`/`PosDef`). The standing assumptions of §4 (p. 70) are carried as hypotheses: strict feasibility of the current pair (which implies strict primal and dual feasibility of the problem) and linear independence of $F_1,\dots,F_m$; $n\ge1$ and $\nu\ge1$ are the domain of (55). If the plane-search minimum is not attained (the algorithm's step 2 cannot be carried out), the hypothesis on $p,q$ cannot be met and the theorem says nothing about that pair. Indices of $F_1,\dots,F_m$ are zero-based.
--
--   Differences from the source:
--   - encoding: the k-th iteration of method 2* → one arbitrary step from a strictly feasible pair with directions solving (66) and an exact plane-search minimizer; reason: every iteration of every run is such a step, so the one-step form is the same statement without assuming an infinite run.
--   - encoding: "minimize φ(x+pδx, Z+qδZ) over p, q ∈ R" → minimality over the real p, q for which the new pair is strictly feasible; reason: φ is only defined there (Lean's `Real.log` is total), and the algorithm's iterates are strictly feasible by construction.
--   - encoding: standing assumptions of §4 and the parameter range ν ≥ 1 of (55) stated once in the section → explicit hypotheses (strictly feasible current pair, F₁,…,Fₘ linearly independent, symmetric data, n ≥ 1, ν ≥ 1); reason: they are the section's assumptions for every result in it, not additions.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 80 (PDF p. 32), Theorem 5.3*; algorithm p. 77 (PDF p. 29); (66) p. 79 (PDF p. 31); standing assumptions p. 70 (PDF p. 22); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsDualSearchDirection
import Definitions.Def_VBSDP_Duality_Supplement_IsPlaneSearchMinimizer

namespace VBSDP.Duality.Supplement

theorem theorem_5_3_star {m n : ℕ} (hn : 0 < n) (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hxZ : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F x Z)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ)
    (hdir : IsDualSearchDirection ν c F₀ F x Z δx δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.05 := by sorry

end VBSDP.Duality.Supplement
