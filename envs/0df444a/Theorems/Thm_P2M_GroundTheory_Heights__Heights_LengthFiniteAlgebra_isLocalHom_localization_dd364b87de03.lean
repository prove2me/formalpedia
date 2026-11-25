-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_isLocalHom_localization_dd364b87de03
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_isLocalHom_localization_dd364b87de03
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:25.322943+00:00
-- url     : https://prove2.me/theorems/84e29fea-dc7c-568e-a7f5-0bf9c113b488
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra is Local Hom localization dd364b87de03: P2 M Ground Theory Heights  Heights Length Finite Algebra is Local Hom localization dd364b87de03
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra is Local Hom localization dd364b87de03 construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra is Local Hom localization dd364b87de03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L52-L62

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

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_isLocalHom_localization_dd364b87de03 [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«isLocalHom_localization» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_isLocalHom_localization_dd364b87de03
