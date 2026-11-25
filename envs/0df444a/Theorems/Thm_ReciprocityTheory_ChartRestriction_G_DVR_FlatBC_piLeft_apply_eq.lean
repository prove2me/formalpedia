-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_piLeft_apply_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.piLeft_apply_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:03.462736+00:00
-- url     : https://prove2.me/theorems/0956baf3-0cd1-4715-81a2-02d77d2dad9e
-- title:
--   Flat BC: pi Left apply eq
-- statement:
--   The Flat BC construction uses the pi Left apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L64-L70

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
omit [Module.Flat R S]

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.piLeft_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Mi : ι → Type*) [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (x : (∀ i, Mi i) ⊗[R] S) (i : ι) :
    (TensorProduct.piLeft (R := R) (N := S) (M := Mi)) x i = (LinearMap.proj i : (∀ i, Mi i) →ₗ[R] Mi i).rTensor S x := by sorry
