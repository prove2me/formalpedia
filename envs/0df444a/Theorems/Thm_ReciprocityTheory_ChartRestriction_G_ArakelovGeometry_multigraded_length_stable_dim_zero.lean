-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_multigraded_length_stable_dim_zero
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.multigraded_length_stable_dim_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:28.626546+00:00
-- url     : https://prove2.me/theorems/accf7ee6-8722-5904-818e-ef061d192233
-- title:
--   Arakelov Geometry: multigraded length stable dim zero
-- statement:
--   The Arakelov Geometry construction uses the multigraded length stable dim zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HilbertMultidegreePieceDivisorSum.lean#L11-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HilbertMultidegreePieceDivisorSum.lean#L11-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HilbertMultidegreePieceDivisorSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.multigraded_length_stable_dim_zero {p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)) (b : K) :
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → lg W a = lg W (a - Pi.single b 1) := by sorry
