-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idx_eq_zero_of_loc
-- name    : PI.Dv.ProjGramW.idx_eq_zero_of_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:10.629493+00:00
-- url     : https://prove2.me/theorems/2a432102-48eb-486b-843c-7f6d776fb893
-- title:
--   Proj Gram W: idx eq zero of loc
-- statement:
--   The Proj Gram W construction uses the idx eq zero of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L54-L62

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

theorem PI.Dv.ProjGramW.idx_eq_zero_of_loc (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hXY : LocLe w 0 X Y) (hYX : LocLe w 0 Y X) : idxAt w X Y = 0 := by sorry
