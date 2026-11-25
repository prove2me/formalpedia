-- Prove2me | Theorems.Thm_PI_WAU_B_half
-- name    : PI.WAU.B.half
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:45:21.21195+00:00
-- url     : https://prove2.me/theorems/89617241-83da-4d8f-b728-ef44d31aca15
-- title:
--   B: half
-- statement:
--   The B construction uses the half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionB.lean#L49-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionB.lean#L49-L89

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

theorem PI.WAU.B.half (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y)
    (j : Fin k) : (I.fmat y⁻¹ * I.fmat x) *ᵥ ivec (F := I.F) (m j) ∈ I.Lf := by sorry
