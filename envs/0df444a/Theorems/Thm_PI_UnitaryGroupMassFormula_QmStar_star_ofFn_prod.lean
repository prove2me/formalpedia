-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_ofFn_prod
-- name    : PI.UnitaryGroupMassFormula.QmStar.star_ofFn_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:25.754347+00:00
-- url     : https://prove2.me/theorems/a3cc5c70-0757-462f-a326-988a2f46a5ff
-- title:
--   Qm Star: star of Fn prod
-- statement:
--   The Qm Star construction uses the star of Fn prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L12-L18

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar

theorem PI.UnitaryGroupMassFormula.QmStar.star_ofFn_prod {A : Type*} [Ring A] [StarRing A] : ∀ {t : ℕ} (f : Fin t → A),
    star (List.ofFn f).prod = (List.ofFn fun i => star (f i.rev)).prod
  := by sorry
