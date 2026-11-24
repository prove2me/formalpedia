-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:14.219514+00:00
-- url     : https://prove2.me/theorems/4eaef3b0-9b25-4752-8c7b-29b8b0c33741
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 up conj  489db79eb27d: P2 M Formalism Fourier Decay Alt P Qx4 up conj  489db79eb27d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 up conj  489db79eb27d construction uses the P2 M Formalism Fourier Decay Alt P Qx4 up conj  489db79eb27d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L196-L198

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d {u p : Mx k r} (hu : u ∈ UP k r l) (hp : p ∈ Glev k r l.succ) : p⁻¹ * u * p ∈ UP k r l := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«up_conj'» := P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d
