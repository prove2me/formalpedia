-- Prove2me | Theorems.Thm_PsdPermanent_projection_log
-- name    : PsdPermanent.projection_log
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:22.564438+00:00
-- url     : https://prove2.me/theorems/50ac85da-f751-4f91-8eda-b6be7f12fa04
-- title:
--   Proof of Theorem 7, p.8 — $v_i^\dagger Z\sim\mathcal{CN}(0,v_i^\dagger Xv_i)$ and its logarithmic moment
-- statement:
--   Let $X$ be Hermitian positive definite, let $Z\sim\mathcal{CN}(0,X)$, and let $v_i\ne0$. Then $s=v_i^\dagger Xv_i>0$,
--   $$v_i^\dagger Z\sim\mathcal{CN}(0,s),$$
--   $\log|v_i^\dagger Z|^2$ is integrable, and
--   $$\mathbb E[\log|v_i^\dagger Z|^2]=\log(v_i^\dagger Xv_i)-\gamma.$$
--
--   Summed over $i$, this is the term that produces the factor $e^{-\gamma n}$ in the lower bound.
--
--   Differences from the source:
--   - encoding: v_i†Xv_i and the law of v_i†Z → the real part of (V X V†)_ii, and the push forward of the density under z ↦ (V z)_i; reason: the same number and the same law
--   - generalization: V the full column rank Gram factor of §3, as in the proof of Theorem 7 → any V with row i nonzero; reason: the law of v_i†Z and its logarithmic moment use only v_i ≠ 0; full column rank factors are a special case
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.8

import Mathlib
import Definitions.Def_PsdPermanent_cnDensity
import Definitions.Def_PsdPermanent_cnScalarDensity
open Matrix
open scoped ComplexOrder
open MeasureTheory

namespace PsdPermanent

/-- **Gaussian projection and its logarithmic moment.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.8: "For the lower bound, take Z ∼ CN(0, X) for an arbitrary X ∈ H_d^{++}. Then v_i† Z ∼ CN(0, v_i† X
v_i), so by Eq. (2), E[log|v_i† Z|²] = log(v_i† X v_i) − γ."

**Formalization Note.** `v_i†Z = (V *ᵥ Z) i` and `v_i†Xv_i = ((V * X * Vᴴ) i i).re`, §3's rows. The law statement is the push
forward under `z ↦ (V *ᵥ z) i`. Integrability is part of the conclusion. The nonzero row is the proof's standing assumption, and
`0 < s` is what makes the scalar law a law. -/
theorem projection_log {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef)
    (i : Fin n) (hi : V i ≠ 0) :
    0 < ((V * X * Vᴴ) i i).re ∧
      (volume.withDensity fun z : Fin d → ℂ => ENNReal.ofReal (cnDensity X z)).map (fun z => (V *ᵥ z) i) =
        volume.withDensity (fun w : ℂ => ENNReal.ofReal (cnScalarDensity ((V * X * Vᴴ) i i).re w)) ∧
      Integrable (fun z : Fin d → ℂ => Real.log (Complex.normSq ((V *ᵥ z) i)) * cnDensity X z) ∧
      (∫ z : Fin d → ℂ, Real.log (Complex.normSq ((V *ᵥ z) i)) * cnDensity X z) =
        Real.log ((V * X * Vᴴ) i i).re - Real.eulerMascheroniConstant := by sorry

end PsdPermanent
