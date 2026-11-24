-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_lattice_iff
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.lattice_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:32.962562+00:00
-- url     : https://prove2.me/theorems/ade70da4-a9c4-4015-a5ef-6405910641e3
-- title:
--   Unimod Loc Std: lattice iff
-- statement:
--   The Unimod Loc Std construction uses the lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L72-L82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.lattice_iff (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by sorry
