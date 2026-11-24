-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:42:05.723446+00:00
-- url     : https://prove2.me/theorems/fd25cfb4-0719-46ac-a7e8-d42004cd8cbb
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 inv inv  225f23d156f5: P2 M Formalism Fourier Decay Alt P Qx4 inv inv  225f23d156f5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 inv inv  225f23d156f5 construction uses the P2 M Formalism Fourier Decay Alt P Qx4 inv inv  225f23d156f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L612-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L612-L612

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

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5 {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«inv_inv'» := P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5
