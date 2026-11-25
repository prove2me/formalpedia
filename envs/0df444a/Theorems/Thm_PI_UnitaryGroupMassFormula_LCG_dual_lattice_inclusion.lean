-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_dual_lattice_inclusion
-- name    : PI.UnitaryGroupMassFormula.LCG.dual_lattice_inclusion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:49.019139+00:00
-- url     : https://prove2.me/theorems/60a9d675-f116-472b-9dca-c3830138c34a
-- title:
--   LCG: dual lattice inclusion
-- statement:
--   The LCG construction uses the dual lattice inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/DualIncl.lean#L78-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/DualIncl.lean#L78-L176

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open DualI Formalism.UG Formalism.UG.P

theorem PI.UnitaryGroupMassFormula.LCG.dual_lattice_inclusion : DualIncl := by sorry
