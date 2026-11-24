-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:05.582597+00:00
-- url     : https://prove2.me/theorems/a7efec04-bf11-4709-9fbd-0d3923d21044
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist twist Sys iff 89a1717ba8b8: P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist twist Sys iff 89a1717ba8b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist twist Sys iff 89a1717ba8b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist twist Sys iff 89a1717ba8b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L195-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L195-L222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8 (F : Kleiman.SubSystem S x E) (c : ℤ) (I : Kleiman.Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (z : E) :
    z ∈ (F.twist (Kleiman.twistSys S x c)).sub I ↔ ∃ y ∈ F.sub I, z = x i ^ c • y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«mem_twist_twistSys_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8
