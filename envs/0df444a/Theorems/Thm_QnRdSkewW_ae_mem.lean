-- Prove2me | Theorems.Thm_QnRdSkewW_ae_mem
-- name    : QnRdSkewW.ae_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:23:33.263186+00:00
-- url     : https://prove2.me/theorems/46ff841a-4e5e-45d2-a0b3-45b465b259fd
-- title:
--   Qn Rd Skew W: ae mem
-- statement:
--   The Qn Rd Skew W construction uses the ae mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/IntegrableOfContOn.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/IntegrableOfContOn.lean#L18-L19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_IntegrableOfContOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}

theorem QnRdSkewW.ae_mem (hconc : μ Gᶜ = 0) : ∀ᵐ x ∂μ, (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) ∈ G := by sorry
