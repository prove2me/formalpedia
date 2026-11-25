-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b
-- name    : P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:21.306214+00:00
-- url     : https://prove2.me/theorems/f96e26de-fbbd-48b8-ba8d-18a64719f83d
-- title:
--   P2 M Formalism Fourier Decay Alt P c2x4 ut inv super  b4a875ff4b5b: P2 M Formalism Fourier Decay Alt P c2x4 ut inv super  b4a875ff4b5b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P c2x4 ut inv super  b4a875ff4b5b construction uses the P2 M Formalism Fourier Decay Alt P c2x4 ut inv super  b4a875ff4b5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L256-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L256-L261

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4

theorem P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a b : Fin m)
    (hb : b.val = a.val + 1) : u⁻¹ a b = -u a b := by sorry

alias «Formalism».«FourierDecayAlt».«P».«c2x4_ut_inv_super'» := P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b
