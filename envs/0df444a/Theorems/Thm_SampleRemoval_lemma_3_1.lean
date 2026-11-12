-- Prove2me | Theorems.Thm_SampleRemoval_lemma_3_1
-- name    : SampleRemoval.lemma_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T05:10:42.940206+00:00
-- url     : https://prove2.me/theorems/d522b803-2812-497f-8ae7-90c598fe3d62
-- title:
--   Lemma 3.1 — single-weight monotonicity
-- statement:
--   Let $w\in[0,1]^n$ and $t\in[n]$, and suppose that $G_0:=\sum_{i\ne t}w_ix_ix_i^{\top}$ is positive definite. For $a\in[0,1]$ let $w^{(a)}$ agree with $w$ except that $w^{(a)}_t=a$, and let $\beta_0=\beta(w^{(0)})$. Then
--
--   1. $\eta:=x_t^{\top}G_0^{-1}x_t\ge0$;
--   2. for every $a\in[0,1]$,
--   $$
--   \beta\bigl(w^{(a)}\bigr)=\beta_0+\frac{a}{1+a\eta}\,\bigl(y_t-x_t^{\top}\beta_0\bigr)\,G_0^{-1}x_t ;
--   $$
--   3. for every $e\in\mathbb R^d$ the map $a\mapsto\langle e,\beta(w^{(a)})\rangle$ is monotone (non-decreasing or non-increasing) on $[0,1]$.
--
--   Changing the weight of a single observation therefore moves every linear functional of the fit monotonically. This is what lets a fractional coordinate be rounded to an endpoint $0$ or $1$ without leaving the feasible set, the key step of the rounding theorem.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
--   - reading: the map a ↦ ⟨e, β(w(a))⟩ is monotone on [0, 1] → MonotoneOn ∨ AntitoneOn on [0, 1], for each e; reason: the direction is the sign of (y_t − x_t⊤β₀)⟨e, G₀⁻¹x_t⟩ and varies with e and the data; the proof shows an affine function of the increasing a/(1 + aη), and the non-decreasing-only reading is false
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Lemma 3.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_SampleRemoval_ols

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- **Lemma 3.1 (Single-weight monotonicity)** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.4). Let `w ∈ [0, 1]ⁿ` and `t ∈ [n]`, and
suppose that `G₀ := Σ_{i≠t} wᵢ xᵢ xᵢ⊤` is positive definite. For `a ∈ [0, 1]` let `w⁽ᵃ⁾` agree
with `w` except that `w⁽ᵃ⁾ₜ = a`, and let `β₀ = β(w⁽⁰⁾)`. Then
`β(w⁽ᵃ⁾) = β₀ + a/(1 + aη) (yₜ − xₜ⊤β₀) G₀⁻¹ xₜ`, `η = xₜ⊤ G₀⁻¹ xₜ ≥ 0`.
In particular, for every `e ∈ ℝᵈ` the map `a ↦ ⟨e, β(w⁽ᵃ⁾)⟩` is monotone on `[0, 1]`.

**Formalization Note** `w⁽ᵃ⁾` is `Function.update w t a`. "Monotone" is read as monotone in
either direction (`MonotoneOn ∨ AntitoneOn` on `[0, 1]`), since the direction depends on the
sign of `(yₜ − xₜ⊤β₀)⟨e, G₀⁻¹xₜ⟩`; the choice of direction may depend on `e`. The matrix
inverse is Mathlib's total one, applied only to the positive definite `G₀`. -/
theorem lemma_3_1 {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (t : Fin n)
    (hG₀ : (∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)).PosDef) :
    let G₀ : Matrix (Fin d) (Fin d) ℝ := ∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)
    let β₀ : Fin d → ℝ := ols x y (Function.update w t 0)
    let η : ℝ := x t ⬝ᵥ (G₀⁻¹ *ᵥ x t)
    0 ≤ η ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, ols x y (Function.update w t a) =
        β₀ + (a / (1 + a * η) * (y t - x t ⬝ᵥ β₀)) • (G₀⁻¹ *ᵥ x t)) ∧
      ∀ e : Fin d → ℝ,
        MonotoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) ∨
          AntitoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) := by sorry

end SampleRemoval
