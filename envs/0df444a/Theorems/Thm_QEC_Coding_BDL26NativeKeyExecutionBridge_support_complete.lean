-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_support_complete
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.support_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:31:31.435029+00:00
-- url     : https://prove2.me/theorems/94402ac0-6f1b-4995-9a2b-223d189ead93
-- title:
--   BDL26 Native Key Execution Bridge: support complete
-- statement:
--   Every original address is present exactly once, including every copy/parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L421-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L421-L453

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeKeyExecutionBridge
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.support_complete (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (support S n J r row).Nodup ∧ (support S n J r row).length = 12 ∧
    ∀ a, a ∈ support S n J r row ↔ SR.decode S n a ∈
      keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by sorry
