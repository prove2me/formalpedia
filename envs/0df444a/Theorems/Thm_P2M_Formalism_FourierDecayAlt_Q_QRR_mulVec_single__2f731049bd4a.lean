-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a
-- name    : P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:32.031664+00:00
-- url     : https://prove2.me/theorems/77f870ee-4559-4da0-8b89-17c57760617f
-- title:
--   P2 M Formalism Fourier Decay Alt Q QRR mul Vec single  2f731049bd4a: P2 M Formalism Fourier Decay Alt Q QRR mul Vec single  2f731049bd4a
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q QRR mul Vec single  2f731049bd4a construction uses the P2 M Formalism Fourier Decay Alt Q QRR mul Vec single  2f731049bd4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RightSingleRule/EllSingleZero.lean#L13-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a (a b : Fin (2 * r + k + 1)) (c : ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) : (Matrix.single a b c *ᵥ z) i = if i = a then c * z b else 0 := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«QRR».«mulVec_single'» := P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a
