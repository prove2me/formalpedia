-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_linIndep_mat
-- name    : PI.Dv.ProjGramW.linIndep_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:17.751862+00:00
-- url     : https://prove2.me/theorems/77f2cbdc-4859-4f2d-9e36-0eaec568e654
-- title:
--   Proj Gram W: lin Indep mat
-- statement:
--   The Proj Gram W construction uses the lin Indep mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L106-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L106-L122

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

theorem PI.Dv.ProjGramW.linIndep_mat {d : ℕ} {b : Fin d → V} (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : LinearIndependent K (fun j => ∑ i, C i j • b i) := by sorry
