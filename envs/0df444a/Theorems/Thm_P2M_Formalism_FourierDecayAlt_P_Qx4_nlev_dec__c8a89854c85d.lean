-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:22.582994+00:00
-- url     : https://prove2.me/theorems/4b7fc484-8128-4b98-8866-8f0467b35ac8
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 nlev dec  c8a89854c85d: P2 M Formalism Fourier Decay Alt P Qx4 nlev dec  c8a89854c85d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 nlev dec  c8a89854c85d construction uses the P2 M Formalism Fourier Decay Alt P Qx4 nlev dec  c8a89854c85d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L697-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L697-L703

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

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) :
    ∃ u ∈ UP k r l, ∃ n₁ ∈ Nlev k r l.succ, n = n₁ * u := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«nlev_dec'» := P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d
