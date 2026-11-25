-- Prove2me | Theorems.Thm_PI_Dv_ProjBW_inner_realize
-- name    : PI.Dv.ProjBW.inner_realize
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:40.091914+00:00
-- url     : https://prove2.me/theorems/4bc934ba-b3f6-4935-9849-451f94861887
-- title:
--   Proj BW: inner realize
-- statement:
--   The Proj BW construction uses the inner realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L21-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
import Theorems.Thm_Formalism_HN_HeightGram_inner_realize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem PI.Dv.ProjBW.inner_realize (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) =
      ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x y).re := by sorry
