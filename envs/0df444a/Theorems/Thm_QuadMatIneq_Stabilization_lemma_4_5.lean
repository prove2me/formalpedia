-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lemma_4_5
-- name    : QuadMatIneq.Stabilization.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:28.602729+00:00
-- url     : https://prove2.me/theorems/1d1f4397-e59d-41a7-bd78-158c4b61a1df
-- title:
--   Lemma 4.5 — for N ∈ 𝚷_{q,r}, x ≠ 0 and [x; y]ᵀN[x; y] ⩾ 0 there is Z ∈ 𝒵_r(N) with y = Zx
-- statement:
--   Let $N\in\boldsymbol\Pi_{q,r}$, and let $x\in\mathbb{R}^q$, $y\in\mathbb{R}^r$ with $x\neq 0$ and
--   $$\begin{bmatrix}x\\ y\end{bmatrix}^{\!\top}N\begin{bmatrix}x\\ y\end{bmatrix}\geqslant 0 .$$
--   Then there exists $Z\in\mathcal Z_r(N)$ such that $y=Zx$.
--
--   This lemma lifts a vector solution of the quadratic inequality defined by $N$ to a matrix solution of the QMI, and is what connects the matrix inclusions of Section 4 with vector-valued implications (Theorem 4.6).
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`. The vector $[x;y]$ is `Sum.elim x y`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma 4.5, p. 10

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Lemma 4.5, p. 10. The vector `[x; y] ∈ ℝ^{q+r}` is `Sum.elim x y`. -/
theorem lemma_4_5 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hN : InPi N) (x : ι → ℝ) (y : κ → ℝ) (hx : x ≠ 0)
    (hxy : 0 ≤ Sum.elim x y ⬝ᵥ (N *ᵥ Sum.elim x y)) :
    ∃ Z ∈ ZSet N, y = Z *ᵥ x := by sorry

end QuadMatIneq.Stabilization
