-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_stdH_apply
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.stdH_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:06.446162+00:00
-- url     : https://prove2.me/theorems/cce6599d-98f2-4cb1-ba58-7e00967168f6
-- title:
--   Unit Det Root: std H apply
-- statement:
--   The Unit Det Root construction uses the std H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L56-L58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.stdH_apply {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.stdH L m x y = ∑ i, x i * ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by sorry
