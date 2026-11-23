-- Prove2me | Theorems.Thm_VBSDP_Duality_Supplement_theorem_5_2
-- name    : VBSDP.Duality.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:10:06.143802+00:00
-- url     : https://prove2.me/theorems/b8a348d7-8e05-4e22-bd09-3ff8a75d3731
-- title:
--   Theorem 5.2 — potential reduction method 1 (directions δxᵖ, δZᵈ) lowers φ by at least 0.78 per iteration
-- statement:
--   Consider the semidefinite program: minimize $c^Tx$ subject to $F(x)=F_0+\sum_{i=1}^mx_iF_i\succeq0$, with data $c\in\mathbb R^m$ and symmetric $F_0,\dots,F_m\in\mathbb R^{n\times n}$, $n\ge1$, and its dual (27): maximize $-\operatorname{Tr}F_0Z$ subject to $Z=Z^T\succeq0$, $\operatorname{Tr}F_iZ=c_i$. Assume that $F_1,\dots,F_m$ are linearly independent. Fix $\nu\ge1$ and the potential (55)
--
--   $$\varphi(x,Z)=\nu\sqrt n\,\log\operatorname{Tr}F(x)Z-\log\det F(x)Z+n\log\operatorname{Tr}F(x)Z-n\log n.$$
--
--   Let $(x,Z)$ be strictly feasible, i.e. $F(x)\succ0$, $Z\succ0$ and $\operatorname{Tr}F_iZ=c_i$ for all $i$, and let $\rho=(n+\nu\sqrt n)/(c^Tx+\operatorname{Tr}F_0Z)$. Let $\delta x=\delta x^p$ be the $x$-part of a solution $(\delta x^p,\delta Z^p)$ of the primal system (64), $F\delta Z^pF+\sum_i\delta x^p_iF_i=-\rho FZF+F$, $\operatorname{Tr}F_j\delta Z^p=0$, and $\delta Z=\delta Z^d$ the $Z$-part of a solution $(\delta x^d,\delta Z^d)$ of the dual system (66), $Z^{-1}\delta Z^dZ^{-1}+\sum_i\delta x^d_iF_i=-\rho F+Z^{-1}$, $\operatorname{Tr}F_j\delta Z^d=0$ (both with symmetric $\delta Z$). Let $p,q\in\mathbb R$ minimize $\varphi(x+p\,\delta x,\,Z+q\,\delta Z)$ over all real step lengths for which the new pair is strictly feasible (the plane search). Then
--
--   $$\varphi(x+p\,\delta x,\;Z+q\,\delta Z)\le\varphi(x,Z)-0.78.$$
--
--   Equivalently, the iterates $x^{(k)},Z^{(k)}$ of the potential reduction algorithm of p. 77 with these search directions satisfy $\varphi(x^{(k+1)},Z^{(k+1)})\le\varphi(x^{(k)},Z^{(k)})-0.78$ at every executed iteration. This is potential reduction method 1 (§5.2); combined with Theorem 5.1 it gives the method a polynomial worst-case iteration bound. The paper refers to Vandenberghe and Boyd [108] for the proof.
--
--   **Formalization Note** The theorem is stated for one arbitrary iteration: every iteration of the algorithm starts from a strictly feasible pair, and the stopping rule (duality gap $\le\epsilon$) only decides whether the step is taken. $\varphi$ is the published `VBSDP.Potential.phi` (the first line of (55)), and the exact plane search is `IsPlaneSearchMinimizer`. "$\ge0$"/"$>0$" for matrices mean positive semidefinite/definite (`PosSemidef`/`PosDef`). The standing assumptions of §4 (p. 70) are carried as hypotheses: strict feasibility of the current pair and linear independence of $F_1,\dots,F_m$; $n\ge1$ and $\nu\ge1$ are the domain of (55). If the plane-search minimum is not attained (step 2 of the algorithm cannot be carried out), the hypothesis on $p,q$ cannot be met and the theorem says nothing about that step. Indices of $F_1,\dots,F_m$ are zero-based.
--
--   Differences from the source:
--   - encoding: the k-th iteration of the algorithm → one arbitrary step from a strictly feasible pair with the named directions and an exact plane-search minimizer; reason: every iteration of every run is such a step, so the one-step form is the same statement without assuming an infinite run.
--   - encoding: "minimize φ(x+pδx, Z+qδZ) over p, q ∈ R" → minimality over the real p, q for which the new pair is strictly feasible; reason: φ is only defined there (Lean's `Real.log` is total), and the algorithm's iterates are strictly feasible by construction.
--   - encoding: standing assumptions of §4 and the parameter range ν ≥ 1 of (55) stated once in the section → explicit hypotheses (strictly feasible current pair, F₁,…,Fₘ linearly independent, symmetric data, n ≥ 1, ν ≥ 1); reason: they are the section's assumptions for every result in it, not additions.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 79 (PDF p. 31), Theorem 5.2; (64) and (66) p. 79; algorithm p. 77 (PDF p. 29); standing assumptions p. 70 (PDF p. 22); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsPrimalSearchDirection
import Definitions.Def_VBSDP_Duality_Supplement_IsDualSearchDirection
import Definitions.Def_VBSDP_Duality_Supplement_IsPlaneSearchMinimizer

namespace VBSDP.Duality.Supplement

theorem theorem_5_2 {m n : ℕ} (hn : 0 < n) (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hxZ : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F x Z)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ)
    (hδx : ∃ δZp : Matrix (Fin n) (Fin n) ℝ, IsPrimalSearchDirection ν c F₀ F x Z δx δZp)
    (hδZ : ∃ δxd : Fin m → ℝ, IsDualSearchDirection ν c F₀ F x Z δxd δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.78 := by sorry

end VBSDP.Duality.Supplement
