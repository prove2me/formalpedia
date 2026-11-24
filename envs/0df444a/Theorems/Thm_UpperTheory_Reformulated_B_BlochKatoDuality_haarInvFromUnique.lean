-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_BlochKatoDuality_haarInvFromUnique
-- name    : UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:58:03.915525+00:00
-- url     : https://prove2.me/theorems/b4dd9881-ee9e-44e8-b734-87e3111934c5
-- title:
--   Bloch Kato Duality: haar Inv From Unique
-- statement:
--   The Bloch Kato Duality construction uses the haar Inv From Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlochKatoDuality.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlochKatoDuality.lean#L8-L45

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapInvolutionEqSelf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurableMatrixInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionMapCompactFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique :
    Formalism.FourierDecayAlt.B2.HaarInvFromUnique := by sorry
