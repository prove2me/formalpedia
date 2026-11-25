-- Prove2me | Theorems.Thm_UpperTheory_GL_oddQS_le
-- name    : UpperTheory.GL.oddQS_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:13:05.050827+00:00
-- url     : https://prove2.me/theorems/61cbf00f-a703-5af9-94d8-afd2d690cc1f
-- title:
--   GL: odd QS le
-- statement:
--   The GL construction uses the odd QS le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/OddQSLe.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/OddQSLe.lean#L7-L24

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_OddQSLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.oddQS_le :
    ∀ {φ : Frame} (H : HostRaw φ) (C : ℝ), (φ.o : ℝ) ≤ C → (H.QS : ℝ) ≤ C * φ.ord → ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C ^ 2 := by sorry
