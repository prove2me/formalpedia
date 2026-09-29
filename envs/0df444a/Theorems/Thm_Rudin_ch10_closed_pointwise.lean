-- Prove2me | Theorems.Thm_Rudin_ch10_closed_pointwise
-- name    : Rudin.ch10_closed_pointwise
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T00:18:38.853678+00:00
-- url     : https://prove2.me/theorems/38ff57be-6b91-4b46-a7ca-979c14d3a883
-- title:
--   A form whose integrals over all surfaces vanish is pointwise closed
-- statement:
--   Let $E \subseteq \mathbb{R}^n$ be open and let $\omega$ be a $(m+1)$-form of class $C'$ in $E$.
--   Suppose that $\int_\Phi d\omega = 0$ for every $C'$ surface $\Phi$ with parameter domain
--   $Q^{m+2}$ whose values lie in $E$ - the integral form of the closedness condition $d\omega = 0$
--   used in Rudin's Definition 10.34.
--
--   The conclusion is that $d\omega$ vanishes pointwise as an alternating form: for every $x \in E$ and
--   every index tuple $i$,
--
--   $$\sum_{\sigma \in S_{m+2}} \operatorname{sgn}(\sigma)\,(d\omega)_{i\circ\sigma}(x) = 0 .$$
--
--   This is the localization step: testing the hypothesis against surfaces that agree, near a point
--   $x \in E$, with a small affine simplex spanned by coordinate directions, and letting the size of
--   that simplex tend to zero, the continuity of the coefficients of $d\omega$ converts the vanishing
--   of all the integrals into the vanishing of the alternating sum at $x$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Definition 10.34 and the discussion of closed and exact forms preceding Theorem 10.39, pp. 275-280

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Chapter 10, Definition 10.34 and Section 10.35: a form all of whose integrals over
surfaces lying in an open set `E` vanish is closed pointwise.  If `ω` is a `(m+1)`-form of class
`C'` in the open set `E` and `∫_Φ dω = 0` for every `C'` surface `Φ` with values in `E`, then the
alternating sum of the coefficients of `dω` vanishes at every point of `E`, i.e. `dω = 0` as an
alternating form. -/
theorem ch10_closed_pointwise (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E)
    (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ Φ : SimplexSurface (m + 1 + 1) n, ContDiff ℝ 1 Φ.map →
      (∀ u, Φ.map u ∈ E) → integralOverSimplex (extDeriv ω) Φ = 0) :
    ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0 := by sorry

end Rudin
