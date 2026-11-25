-- Prove2me | Theorems.Thm_P2M_PI_Dv_ProjGramW_vAdd_zero__1a796c960964
-- name    : P2M_PI_Dv_ProjGramW_vAdd_zero__1a796c960964
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:56:14.061156+00:00
-- url     : https://prove2.me/theorems/4da56533-6c37-4436-abbf-85208e9ed1a1
-- title:
--   P2 M PI Dv Proj Gram W v Add zero  1a796c960964: P2 M PI Dv Proj Gram W v Add zero  1a796c960964
-- statement:
--   The P2 M PI Dv Proj Gram W v Add zero  1a796c960964 construction uses the P2 M PI Dv Proj Gram W v Add zero  1a796c960964 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean#L72-L73

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

theorem P2M_PI_Dv_ProjGramW_vAdd_zero__1a796c960964 (w : HeightOneSpectrum (𝓞 K)) : vAdd w (0 : K) = 0 := by sorry

alias «PI».«Dv».«ProjGramW».«vAdd_zero'» := P2M_PI_Dv_ProjGramW_vAdd_zero__1a796c960964
