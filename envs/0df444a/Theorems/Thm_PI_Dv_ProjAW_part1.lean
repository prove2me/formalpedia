-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_part1
-- name    : PI.Dv.ProjAW.part1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:29.16579+00:00
-- url     : https://prove2.me/theorems/fd30fa79-6a2f-4141-a6ef-9f74342f39ac
-- title:
--   Proj AW: part1
-- statement:
--   The Proj AW construction uses the part1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L41-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)

theorem PI.Dv.ProjAW.part1 {f : Module.End K A.V} {n : ℕ} (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    ∀ x ∈ imgE A f A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A f A.L := by sorry
