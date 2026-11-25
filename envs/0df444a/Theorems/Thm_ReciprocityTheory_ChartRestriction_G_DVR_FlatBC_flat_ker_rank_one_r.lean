-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_flat_ker_rank_one_r
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one_r
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:48.602224+00:00
-- url     : https://prove2.me/theorems/c9d95396-7638-4a99-a267-d94775deeb23
-- title:
--   Flat BC: flat ker rank one r
-- statement:
--   The Flat BC construction uses the flat ker rank one r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L47-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one_r (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : M ⊗[R] S) (ht : δ.rTensor S t = 0) :
    ∃! a : S, t = θ ⊗ₜ[R] a := by sorry
