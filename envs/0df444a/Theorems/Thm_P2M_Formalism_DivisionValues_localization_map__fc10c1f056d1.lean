-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1
-- name    : P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:33.472678+00:00
-- url     : https://prove2.me/theorems/89aa5694-75d5-4e95-b8a0-4e2e3ab5da8f
-- title:
--   P2 M Formalism Division Values localization map  fc10c1f056d1: P2 M Formalism Division Values localization map  fc10c1f056d1
-- statement:
--   The P2 M Formalism Division Values localization map  fc10c1f056d1 construction uses the P2 M Formalism Division Values localization map  fc10c1f056d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L20-L32

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1 (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (f : W →ₗ[R] W)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (f : W →ₗ[R] W) := by sorry

alias «Formalism».«DivisionValues».«localization_map'» := P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1
