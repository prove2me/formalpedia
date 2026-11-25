-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__sigA_le_84a71e82304c
-- name    : P2M_UpperTheory_Comparison__sigA_le_84a71e82304c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:12.405113+00:00
-- url     : https://prove2.me/theorems/99ebed93-d822-4394-8e42-71b24493968a
-- title:
--   P2 M Upper Theory Comparison  sig A le 84a71e82304c: P2 M Upper Theory Comparison  sig A le 84a71e82304c
-- statement:
--   The P2 M Upper Theory Comparison  sig A le 84a71e82304c construction uses the P2 M Upper Theory Comparison  sig A le 84a71e82304c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean#L38-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean#L38-L60

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CardPsiA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_SigALe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem P2M_UpperTheory_Comparison__sigA_le_84a71e82304c :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤ 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by sorry

alias «UpperTheory».«Comparison₂».«sigA_le» := P2M_UpperTheory_Comparison__sigA_le_84a71e82304c
