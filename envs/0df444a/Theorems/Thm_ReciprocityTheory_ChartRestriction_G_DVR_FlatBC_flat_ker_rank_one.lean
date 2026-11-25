-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_flat_ker_rank_one
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:27.301816+00:00
-- url     : https://prove2.me/theorems/5b761bb3-546e-5860-b92f-8c4d06802844
-- title:
--   Flat BC: flat ker rank one
-- statement:
--   The Flat BC construction uses the flat ker rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L17-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L17-L45

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : S ⊗[R] M) (ht : δ.lTensor S t = 0) :
    ∃! a : S, t = a ⊗ₜ[R] θ := by sorry
