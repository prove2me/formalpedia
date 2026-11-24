-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:17.216325+00:00
-- url     : https://prove2.me/theorems/d8e29d2a-a422-4970-9f49-6244c235529d
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 stab dec  b3b71b5cc842: P2 M Formalism Fourier Decay Alt P Qx4 stab dec  b3b71b5cc842
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 stab dec  b3b71b5cc842 construction uses the P2 M Formalism Fourier Decay Alt P Qx4 stab dec  b3b71b5cc842 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L317-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L317-L321

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

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842 {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) :
    ∃ u ∈ UP k r l, ∃ g₁ ∈ Glev k r l.succ, g = g₁ * u := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«stab_dec'» := P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
