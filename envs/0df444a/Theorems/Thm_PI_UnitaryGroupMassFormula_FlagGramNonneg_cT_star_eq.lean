-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_cT_star_eq
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.cT_star_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:45.554625+00:00
-- url     : https://prove2.me/theorems/82fd542c-ab98-4c82-8e36-b3961f834deb
-- title:
--   Flag Gram Nonneg: c T star eq
-- statement:
--   The Flag Gram Nonneg construction uses the c T star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/HasSignatureExistsNonneg.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/HasSignatureExistsNonneg.lean#L10-L12

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_HasSignatureExistsNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.cT_star_eq {m n : Type} (M : Matrix m n ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by sorry
