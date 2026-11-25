-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotSectionsFinite_proof_34f97c5bf3c0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotSectionsFinite_proof_34f97c5bf3c0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:42.634287+00:00
-- url     : https://prove2.me/theorems/7b00bbda-b50f-5a8a-8f1c-1b04b1e61959
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quot Sections Finite proof 34f97c5bf3c0: P2 M Ground Theory Heights  Heights Kleiman Quot Sections Finite proof 34f97c5bf3c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quot Sections Finite proof 34f97c5bf3c0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Quot Sections Finite proof 34f97c5bf3c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotSectionsFinite.lean#L19-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotSectionsFinite.lean#L19-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotSectionsFinite
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
universe u w
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotSectionsFinite_proof_34f97c5bf3c0 (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotSectionsFinite».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotSectionsFinite_proof_34f97c5bf3c0
