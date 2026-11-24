-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:17.346001+00:00
-- url     : https://prove2.me/theorems/7b0e4981-09e3-4ac9-93d7-aed8da828442
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact decompose map 2289620b9997: P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact decompose map 2289620b9997
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact decompose map 2289620b9997 construction uses the P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact decompose map 2289620b9997 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L15-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.DegLocExact

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997 {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DegLocExact».«decompose_map» := P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_decompose_map_2289620b9997
