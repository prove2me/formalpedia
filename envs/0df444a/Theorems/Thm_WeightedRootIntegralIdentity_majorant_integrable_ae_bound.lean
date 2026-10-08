-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_majorant_integrable_ae_bound
-- name    : WeightedRootIntegralIdentity.majorant_integrable_ae_bound
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T09:32:01.70696+00:00
-- url     : https://prove2.me/theorems/f6dd99a3-17b2-4714-9ac4-90ffecc93e66
-- title:
--   Compact-interval integrability and almost-everywhere domination
-- statement:
--   A continuous majorant on a compact interval is integrable there, and any pointwise bound by that majorant yields the corresponding almost-everywhere bound under restricted Lebesgue measure.
-- source:
--   Continuous functions are integrable on compact sets; restricting a pointwise inequality gives an almost-everywhere statement.

import Mathlib
open MeasureTheory

namespace WeightedRootIntegralIdentity
open MeasureTheory

theorem majorant_integrable_ae_bound {f g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.uIcc a b))
    (hbound : ∀ x ∈ Set.uIcc a b, ‖f x‖ ≤ g x) :
    IntegrableOn g (Set.uIcc a b) ∧
      ∀ᵐ x ∂Measure.restrict volume (Set.uIcc a b),
        ‖f x‖ ≤ g x := by sorry

end WeightedRootIntegralIdentity
