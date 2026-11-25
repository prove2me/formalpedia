-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__gmA_eq_3f2fbc7b3a37
-- name    : P2M_UpperTheory_Comparison__gmA_eq_3f2fbc7b3a37
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:16.362672+00:00
-- url     : https://prove2.me/theorems/49e6e1c0-a632-5076-8374-ed2a73655ff7
-- title:
--   P2 M Upper Theory Comparison  gm A eq 3f2fbc7b3a37: P2 M Upper Theory Comparison  gm A eq 3f2fbc7b3a37
-- statement:
--   The P2 M Upper Theory Comparison  gm A eq 3f2fbc7b3a37 construction uses the P2 M Upper Theory Comparison  gm A eq 3f2fbc7b3a37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean#L61-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean#L61-L149

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimInj
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ChrBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GzEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GmAEq
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

theorem P2M_UpperTheory_Comparison__gmA_eq_3f2fbc7b3a37 :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by sorry

alias «UpperTheory».«Comparison₂».«gmA_eq» := P2M_UpperTheory_Comparison__gmA_eq_3f2fbc7b3a37
