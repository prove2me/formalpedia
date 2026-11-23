-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_inv_mem_UFin
-- name    : PI.AlgValsFin.W.inv_mem_UFin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:32.416606+00:00
-- url     : https://prove2.me/theorems/b223001e-5ea6-48dd-9cc6-36d1de2f10db
-- title:
--   W: inv mem UFin
-- statement:
--   The W construction uses the inv mem UFin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L30-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.inv_mem_UFin {x : Ideles L} (hx : x ∈ UFin L) : x⁻¹ ∈ UFin L := by sorry
