-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_hform_add_right
-- name    : PI.UnitaryGroupMassFormula.LCG.DualI.hform_add_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:47.458551+00:00
-- url     : https://prove2.me/theorems/eca1241e-2d6c-4e48-97f8-33be7444a809
-- title:
--   Dual I: hform add right
-- statement:
--   The Dual I construction uses the hform add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/DualIncl.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/DualIncl.lean#L41-L44

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
open PI.UnitaryGroupMassFormula.LCG.DualI
open Formalism.UG Formalism.UG.P

theorem PI.UnitaryGroupMassFormula.LCG.DualI.hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x + x') = hform τ J w x + hform τ J w x' := by sorry
