-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjW__4b27e7c5ccdf
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjW__4b27e7c5ccdf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:14.444198+00:00
-- url     : https://prove2.me/theorems/cd6e29e0-2afd-4ee0-a189-5c2a9d71c8a6
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx4 psi conj W  4b27e7c5ccdf: P2 M Formalism Fourier Decay Alt P Qx4 psi conj W  4b27e7c5ccdf
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx4 psi conj W  4b27e7c5ccdf construction uses the P2 M Formalism Fourier Decay Alt P Qx4 psi conj W  4b27e7c5ccdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L731-L734
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L731-L734

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

theorem P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjW__4b27e7c5ccdf {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h u : Mx k r} (hh : h ∈ UWset k r z) (hu : u ∈ Nset k r) :
    psi k r z cStd (h⁻¹ * u * h) = psi k r z cStd u := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx4».«psi_conjW'» := P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjW__4b27e7c5ccdf
