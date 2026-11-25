-- Prove2me | Theorems.Thm_UpperTheory_GL_isInert_iff
-- name    : UpperTheory.GL.isInert_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:06:27.08267+00:00
-- url     : https://prove2.me/theorems/2b1639b6-7ea8-503d-8a00-f6d9cc84230c
-- title:
--   GL: is Inert iff
-- statement:
--   The GL construction uses the is Inert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/IsInertIff.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/IsInertIff.lean#L35-L44

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_IsInertIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.isInert_iff :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), IsInert (arith H.toHostRaw) p ↔ p.Prime ∧ ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 := by sorry
