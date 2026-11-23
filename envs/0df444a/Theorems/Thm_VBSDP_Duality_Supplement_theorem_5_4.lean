-- Prove2me | Theorems.Thm_VBSDP_Duality_Supplement_theorem_5_4
-- name    : VBSDP.Duality.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:12:54.113584+00:00
-- url     : https://prove2.me/theorems/73f30121-fd3a-4a61-976b-2b8476913383
-- title:
--   Theorem 5.4 — potential reduction method 3 (Nesterov–Todd directions δxˢʸᵐ, δZˢʸᵐ) lowers φ by at least 0.24 per iteration
-- statement:
--   Consider the semidefinite program: minimize $c^Tx$ subject to $F(x)=F_0+\sum_{i=1}^mx_iF_i\succeq0$, with data $c\in\mathbb R^m$ and symmetric $F_0,\dots,F_m\in\mathbb R^{n\times n}$, $n\ge1$, and its dual (27): maximize $-\operatorname{Tr}F_0Z$ subject to $Z=Z^T\succeq0$, $\operatorname{Tr}F_iZ=c_i$. Assume that $F_1,\dots,F_m$ are linearly independent. Fix $\nu\ge1$ and the potential (55)
--
--   $$\varphi(x,Z)=\nu\sqrt n\,\log\operatorname{Tr}F(x)Z-\log\det F(x)Z+n\log\operatorname{Tr}F(x)Z-n\log n.$$
--
--   Let $(x,Z)$ be strictly feasible, i.e. $F(x)\succ0$, $Z\succ0$ and $\operatorname{Tr}F_iZ=c_i$ for all $i$, and let $\rho=(n+\nu\sqrt n)/(c^Tx+\operatorname{Tr}F_0Z)$. Let $(\delta x,\delta Z)=(\delta x^{\rm sym},\delta Z^{\rm sym})$ solve the symmetric system of §5.4, $RR^T\delta Z^{\rm sym}RR^T+\sum_i\delta x^{\rm sym}_iF_i=-\rho F+Z^{-1}$, $\operatorname{Tr}F_j\delta Z^{\rm sym}=0$, with $\delta Z^{\rm sym}$ symmetric, where $R^TF^{-1}R=\Lambda^{-1/2}$, $R^TZR=\Lambda^{1/2}$ and $F^{1/2}ZF^{1/2}=U\Lambda U^T$, $R=F^{1/2}U\Lambda^{-1/4}$. Let $p,q\in\mathbb R$ minimize $\varphi(x+p\,\delta x,\,Z+q\,\delta Z)$ over all real step lengths for which the new pair is strictly feasible (the plane search). Then
--
--   $$\varphi(x+p\,\delta x,\;Z+q\,\delta Z)\le\varphi(x,Z)-0.24.$$
--
--   Equivalently, the iterates $x^{(k)},Z^{(k)}$ of the potential reduction algorithm of p. 77 with these search directions satisfy $\varphi(x^{(k+1)},Z^{(k+1)})\le\varphi(x^{(k)},Z^{(k)})-0.24$ at every executed iteration. This is potential reduction method 3 (§5.4), due to Nesterov and Todd [77], to whom the paper attributes the proof.
--
--   **Formalization Note** The theorem is stated for one arbitrary iteration: every iteration of the algorithm starts from a strictly feasible pair, and the stopping rule (duality gap $\le\epsilon$) only decides whether the step is taken. $\varphi$ is the published `VBSDP.Potential.phi` (the first line of (55)), and the exact plane search is `IsPlaneSearchMinimizer`. "$\ge0$"/"$>0$" for matrices mean positive semidefinite/definite (`PosSemidef`/`PosDef`). The standing assumptions of §4 (p. 70) are carried as hypotheses: strict feasibility of the current pair and linear independence of $F_1,\dots,F_m$; $n\ge1$ and $\nu\ge1$ are the domain of (55). If the plane-search minimum is not attained (step 2 of the algorithm cannot be carried out), the hypothesis on $p,q$ cannot be met and the theorem says nothing about that step. Indices of $F_1,\dots,F_m$ are zero-based. The scaling $RR^T$ enters through `IsSymmetricSearchDirection` as the unique positive definite $W$ with $WZW=F(x)$, which is what the page's two relations for $R$ give.
--
--   Differences from the source:
--   - encoding: the k-th iteration of the algorithm → one arbitrary step from a strictly feasible pair with the named directions and an exact plane-search minimizer; reason: every iteration of every run is such a step, so the one-step form is the same statement without assuming an infinite run.
--   - encoding: "minimize φ(x+pδx, Z+qδZ) over p, q ∈ R" → minimality over the real p, q for which the new pair is strictly feasible; reason: φ is only defined there (Lean's `Real.log` is total), and the algorithm's iterates are strictly feasible by construction.
--   - encoding: standing assumptions of §4 and the parameter range ν ≥ 1 of (55) stated once in the section → explicit hypotheses (strictly feasible current pair, F₁,…,Fₘ linearly independent, symmetric data, n ≥ 1, ν ≥ 1); reason: they are the section's assumptions for every result in it, not additions.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 81 (PDF p. 33), Theorem 5.4; symmetric system p. 80 (PDF p. 32); algorithm p. 77 (PDF p. 29); standing assumptions p. 70 (PDF p. 22); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsSymmetricSearchDirection
import Definitions.Def_VBSDP_Duality_Supplement_IsPlaneSearchMinimizer

namespace VBSDP.Duality.Supplement

theorem theorem_5_4 {m n : ℕ} (hn : 0 < n) (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hxZ : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F x Z)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ)
    (hdir : IsSymmetricSearchDirection ν c F₀ F x Z δx δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.24 := by sorry

end VBSDP.Duality.Supplement
