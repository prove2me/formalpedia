-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_locLe_zero_iff
-- name    : PI.Dv.ProjGramW.locLe_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:53.539663+00:00
-- url     : https://prove2.me/theorems/f253ed72-a50b-49b9-b000-48e9f5dc9241
-- title:
--   Proj Gram W: loc Le zero iff
-- statement:
--   The Proj Gram W construction uses the loc Le zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L29-L32

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

theorem PI.Dv.ProjGramW.locLe_zero_iff (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) :
    LocLe w 0 X Y ↔ ∀ x ∈ X, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y := by sorry
