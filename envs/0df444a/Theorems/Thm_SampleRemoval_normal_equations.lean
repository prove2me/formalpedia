-- Prove2me | Theorems.Thm_SampleRemoval_normal_equations
-- name    : SampleRemoval.normal_equations
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:10:30.227765+00:00
-- url     : https://prove2.me/theorems/bb74ae02-8db0-4e54-8c08-bab6578b06b3
-- title:
--   §2 — $\beta(w)$ is the unique solution of the normal equations
-- statement:
--   Let $(x_i,y_i)\in\mathbb R^d\times\mathbb R$, $i\in[n]$, be observations and let $w\in[0,1]^n$ be a weight vector whose Gram matrix $G(w)=\sum_i w_ix_ix_i^{\top}$ is positive definite. Then for every $b\in\mathbb R^d$,
--
--   $$
--   \sum_{i=1}^n w_i\,x_i\,(y_i-x_i^{\top}b)=0\iff b=\beta(w)=G(w)^{-1}g(w).
--   $$
--
--   That is, the weighted least-squares estimate is the unique solution of the weighted normal equations. The paper uses this characterisation to recognise $\beta(w')=\beta(w)$ for a re-weighting $w'$ with the same residual balance (Lemma 3.2).
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Weighted least squares, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_ols

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- **§2, Weighted least squares** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.3): "The estimate β(w) is equivalently characterised
as the unique solution of the normal equations Σᵢ wᵢxᵢ(yᵢ − xᵢ⊤β) = 0."

For `w ∈ [0, 1]ⁿ` with `G(w) ≻ 0`, a vector `b ∈ ℝᵈ` solves the normal equations if and only if
`b = β(w)`.

**Formalization Note** "Unique solution" is the equivalence for every `b`: `β(w)` solves the
equations, and every solution equals `β(w)`. `x` is `Fin n → Fin d → ℝ` with paper index
`i` = Lean index `i − 1`. -/
theorem normal_equations {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (hG : (gram x w).PosDef) (b : Fin d → ℝ) :
    ∑ i, (w i * (y i - x i ⬝ᵥ b)) • x i = 0 ↔ b = ols x y w := by sorry

end SampleRemoval
