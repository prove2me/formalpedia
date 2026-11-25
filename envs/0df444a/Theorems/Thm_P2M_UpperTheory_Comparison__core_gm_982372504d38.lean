-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__core_gm_982372504d38
-- name    : P2M_UpperTheory_Comparison__core_gm_982372504d38
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:04.560883+00:00
-- url     : https://prove2.me/theorems/388b7140-e314-4df7-a794-16b05612c758
-- title:
--   P2 M Upper Theory Comparison  core gm 982372504d38: P2 M Upper Theory Comparison  core gm 982372504d38
-- statement:
--   The P2 M Upper Theory Comparison  core gm 982372504d38 construction uses the P2 M Upper Theory Comparison  core gm 982372504d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L12-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L12-L74

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_charsA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GmAEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_SigALe
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreGm
import Theorems.Thm_P2M_UpperTheory_Comparison__charsA_aeb36eedc800
import Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c

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

theorem P2M_UpperTheory_Comparison__core_gm_982372504d38 :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by sorry

alias «UpperTheory».«Comparison₂».«core_gm» := P2M_UpperTheory_Comparison__core_gm_982372504d38
