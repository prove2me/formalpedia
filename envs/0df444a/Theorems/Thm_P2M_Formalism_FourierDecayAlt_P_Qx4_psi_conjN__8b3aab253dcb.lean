-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:44:34.574685+00:00
-- url     : https://prove2.me/theorems/bcc8c062-2766-4a5b-b3f6-dc58ea5296a7
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 psi conj N  8b3aab253dcb: P2 M Formalism Fourier Decay Alt P Qx4 psi conj N  8b3aab253dcb
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 psi conj N  8b3aab253dcb construction uses the P2 M Formalism Fourier Decay Alt P Qx4 psi conj N  8b3aab253dcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L721-L724
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L721-L724

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

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n u : Mx k r} (hn : n ∈ Nset k r) (hu : u ∈ Nset k r) :
    psi k r z cStd (n⁻¹ * u * n) = psi k r z cStd u := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«psi_conjN'» := P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb
