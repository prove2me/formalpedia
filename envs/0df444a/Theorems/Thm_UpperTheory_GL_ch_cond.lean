-- Prove2me | Theorems.Thm_UpperTheory_GL_ch_cond
-- name    : UpperTheory.GL.ch_cond
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:44:06.261656+00:00
-- url     : https://prove2.me/theorems/474002eb-9afc-4289-8bba-138110faa320
-- title:
--   GL: ch cond
-- statement:
--   The GL construction uses the ch cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/ChCond.lean#L92-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/ChCond.lean#L92-L153

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_ChCond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.ch_cond :
    ∀ {φ : Frame} (H : HostAx φ), (dirChar (recH H.toHostRaw) chC).conductor = H.d ∧
      (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chC n = ((jacobiSym (n : ℤ) H.d : ℤ) : ℂ)) ∧
      (H.PsQ → (dirChar (recH H.toHostRaw) psC).conductor = H.q ∧
        (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) psC n = ((jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) ∧
        ∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chpsC n = ((jacobiSym (n : ℤ) H.d * jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) := by sorry
