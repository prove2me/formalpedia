-- Prove2me | Theorems.Thm_PI_WAU_B_step
-- name    : PI.WAU.B.step
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:39.081223+00:00
-- url     : https://prove2.me/theorems/efb3e57e-27af-4cd7-a1fa-38aad42cc1ed
-- title:
--   B: step
-- statement:
--   The B construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionB.lean#L91-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionB.lean#L91-L107

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)

theorem PI.WAU.B.step (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y) :
    y⁻¹ * x ∈ I.Kset := by sorry
