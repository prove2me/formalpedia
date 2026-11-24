-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:28.255505+00:00
-- url     : https://prove2.me/theorems/821a66f3-5c79-4fe5-a7d1-9348ef990cf3
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra finite maximal Spectrum 4974b2542461: P2 M Ground Theory Heights  Heights Length Finite Algebra finite maximal Spectrum 4974b2542461
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra finite maximal Spectrum 4974b2542461 construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra finite maximal Spectrum 4974b2542461 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L19-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461 [Module.Finite O B] : Finite (MaximalSpectrum B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«finite_maximalSpectrum» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461
