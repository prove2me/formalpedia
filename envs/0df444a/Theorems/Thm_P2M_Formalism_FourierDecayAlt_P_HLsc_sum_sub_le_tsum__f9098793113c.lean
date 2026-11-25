-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum__f9098793113c
-- name    : P2M_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum__f9098793113c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:28.639152+00:00
-- url     : https://prove2.me/theorems/b088a7b4-07fd-46cf-a296-64adff48505c
-- title:
--   P2 M Formalism Fourier Decay Alt P HLsc sum sub le tsum  f9098793113c: P2 M Formalism Fourier Decay Alt P HLsc sum sub le tsum  f9098793113c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P HLsc sum sub le tsum  f9098793113c construction uses the P2 M Formalism Fourier Decay Alt P HLsc sum sub le tsum  f9098793113c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L66-L70

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum__f9098793113c {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (σ' : Fin d → ℤ) :
    ∑ σ ∈ B, κ (σ - σ') ≤ ∑' τ, κ τ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HLsc».«sum_sub_le_tsum'» := P2M_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum__f9098793113c
