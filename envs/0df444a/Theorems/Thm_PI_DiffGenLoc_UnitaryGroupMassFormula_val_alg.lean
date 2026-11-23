-- Prove2me | Theorems.Thm_PI_DiffGenLoc_UnitaryGroupMassFormula_val_alg
-- name    : PI.DiffGenLoc.UnitaryGroupMassFormula.val_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:53.729916+00:00
-- url     : https://prove2.me/theorems/74359c50-5c46-4dc3-9e38-7896f55f87ec
-- title:
--   Unitary Group Mass Formula: val alg
-- statement:
--   The Unitary Group Mass Formula construction uses the val alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDifferentGenerators/DiffExistsMain.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDifferentGenerators/DiffExistsMain.lean#L10-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDifferentGenerators_DiffExistsMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DiffGenLoc PI.DiffGenLoc.UnitaryGroupMassFormula
open NumberField IsDedekindDomain WithZero

theorem PI.DiffGenLoc.UnitaryGroupMassFormula.val_alg {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by sorry
