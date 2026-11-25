-- Prove2me | Theorems.Thm_UpperTheory_GL_kronecker
-- name    : UpperTheory.GL.kronecker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:01:59.437673+00:00
-- url     : https://prove2.me/theorems/ca805190-82dd-4686-9cfb-3c4915e5873b
-- title:
--   GL: kronecker
-- statement:
--   The GL construction uses the kronecker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/kronecker.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/kronecker.lean#L17-L32

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_kronecker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.kronecker :
    ∀ {φ : Frame} (H : HostAx φ) (m : ℕ) (hm : m.Coprime H.condN),
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 0 ↔ jacobiSym (-(H.d : ℤ)) m = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 1 ↔ jacobiSym (-(H.d : ℤ)) m = -1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = -1) ∧
      (H.PsQ → ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ jacobiSym (-(H.q : ℤ)) m = 1) ∧
        ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ jacobiSym (-(H.q : ℤ)) m = -1)) ∧
      (recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.2 = φ.iotaInv (H.art (ZMod.unitOfCoprime m hm)).2 := by sorry
