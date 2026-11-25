-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:29.726228+00:00
-- url     : https://prove2.me/theorems/a177b861-3db1-49e1-9167-9ac10d7ee254
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx2 unit col  f12299f6bc02: P2 M Formalism Fourier Decay Alt P Qx2 unit col  f12299f6bc02
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx2 unit col  f12299f6bc02 construction uses the P2 M Formalism Fourier Decay Alt P Qx2 unit col  f12299f6bc02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L180-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L180-L193

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02 {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (ha : inV k r i a) (hp : ¬ inV k r i p) :
    (Hpk k r * (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ * Hpk k r) *ᵥ bvec p = 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx2».«unit_col'» := P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02
