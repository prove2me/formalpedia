-- Prove2me | Theorems.Thm_PI_ET_HornW_key
-- name    : PI.ET.HornW.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:50.172437+00:00
-- url     : https://prove2.me/theorems/739479dc-78f3-40d1-9d13-d4bf2278a6ef
-- title:
--   Horn W: key
-- statement:
--   The Horn W construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L207-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L207-L247

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}

theorem PI.ET.HornW.key (hK : KyFanDet) {Wx Wy Wz : Matrix (Fin n) (Fin n) ℂ}
    (hWx : Wx ∈ unitaryGroup (Fin n) ℂ) (hWy : Wy ∈ unitaryGroup (Fin n) ℂ)
    (hWz : Wz ∈ unitaryGroup (Fin n) ℂ) {ξ η ζ : Fin n → ℝ} (hξ : Antitone ξ) (hη : Antitone η)
    (hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) *
        (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) =
      (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) *
        ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) *
          (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) *
        (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))
    (k : ℕ) (hk : k ≤ n) :
    psum ζ k ≤ psum (fun i => ξ i + η i) k := by sorry
