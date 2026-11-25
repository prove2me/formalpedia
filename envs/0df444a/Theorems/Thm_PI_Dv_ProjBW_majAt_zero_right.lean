-- Prove2me | Theorems.Thm_PI_Dv_ProjBW_majAt_zero_right
-- name    : PI.Dv.ProjBW.majAt_zero_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:39.477252+00:00
-- url     : https://prove2.me/theorems/8f788a1b-ad96-5c95-893c-34d0c0f9cac5
-- title:
--   Proj BW: maj At zero right
-- statement:
--   The Proj BW construction uses the maj At zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L33-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
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

theorem PI.Dv.ProjBW.majAt_zero_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : Formalism.HermitianLatticesTheory.majAt b X v x 0 = 0 := by sorry
