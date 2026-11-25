-- Prove2me | Theorems.Thm_PI_VolStabSW_DiscreteGroups_approx
-- name    : PI.VolStabSW.DiscreteGroups.approx
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:04.990827+00:00
-- url     : https://prove2.me/theorems/41cdf5fd-d747-41a8-96a2-7538dfcb4b64
-- title:
--   Discrete Groups: approx
-- statement:
--   The Discrete Groups construction uses the approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibDis.lean#L30-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibDis.lean#L30-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

theorem PI.VolStabSW.DiscreteGroups.approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by sorry
