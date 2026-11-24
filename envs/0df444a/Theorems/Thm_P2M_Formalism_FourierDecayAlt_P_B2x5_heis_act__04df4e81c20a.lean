-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:16.960865+00:00
-- url     : https://prove2.me/theorems/b2c8b32d-82ef-4264-af2e-637c831d9e29
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x5 heis act  04df4e81c20a: P2 M Formalism Fourier Decay Alt P B2x5 heis act  04df4e81c20a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x5 heis act  04df4e81c20a construction uses the P2 M Formalism Fourier Decay Alt P B2x5 heis act  04df4e81c20a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L321-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L321-L324

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' (liftVec k 1 r' y) b *ᵥ u =
      u - herm (Hpk k r') (res k r' u) y • e0 k r' + u (iL k r') • (liftVec k 1 r' y + b • e0 k r') := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x5».«heis_act'» := P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
