-- Prove2me | Theorems.Thm_PI_Dv_GLP_char_orth
-- name    : PI.Dv.GLP.char_orth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:10.706265+00:00
-- url     : https://prove2.me/theorems/b7d3bdf2-550b-5db6-92c1-73052ac8ef94
-- title:
--   GLP: char orth
-- statement:
--   The GLP construction uses the char orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L107-L118

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLP.char_orth [CharZero K] (T : GoodSet K G) (s t : T.S) :
    ∑ g : G, LinearMap.trace K _ (T.tau t g) * LinearMap.trace K _ (T.tau s g⁻¹) =
      if s = t then ((Fintype.card G : ℕ) : K) else 0 := by sorry
