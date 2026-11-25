-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idx_nonpos_of_loc
-- name    : PI.Dv.ProjGramW.idx_nonpos_of_loc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:26.20602+00:00
-- url     : https://prove2.me/theorems/9aa60a0b-bc13-4541-b91b-a3cbc1dafbd3
-- title:
--   Proj Gram W: idx nonpos of loc
-- statement:
--   The Proj Gram W construction uses the idx nonpos of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L64-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.idx_nonpos_of_loc (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V))
    (hXY : LocLe w 0 X Y) : idxAt w X Y ≤ 0 := by sorry
