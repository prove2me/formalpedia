-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:31.482772+00:00
-- url     : https://prove2.me/theorems/7872daf1-8756-431d-8329-d8532e1a894d
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra length eq finsum localization 30845086f09f: P2 M Ground Theory Heights  Heights Length Finite Algebra length eq finsum localization 30845086f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra length eq finsum localization 30845086f09f construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra length eq finsum localization 30845086f09f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L27-L50

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

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«length_eq_finsum_localization» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f
