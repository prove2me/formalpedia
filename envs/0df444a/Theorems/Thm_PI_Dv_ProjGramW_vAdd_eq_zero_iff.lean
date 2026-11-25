-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_vAdd_eq_zero_iff
-- name    : PI.Dv.ProjGramW.vAdd_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:34.918413+00:00
-- url     : https://prove2.me/theorems/aecadcb7-be20-4ac8-a475-3b02748ab09c
-- title:
--   Proj Gram W: v Add eq zero iff
-- statement:
--   The Proj Gram W construction uses the v Add eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L92-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L92-L104

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

theorem PI.Dv.ProjGramW.vAdd_eq_zero_iff (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs0 : s ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K s) = 0 ↔ s ∉ w.asIdeal := by sorry
