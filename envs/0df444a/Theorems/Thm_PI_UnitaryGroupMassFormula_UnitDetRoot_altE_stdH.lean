-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_altE_stdH
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.altE_stdH
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:24.493065+00:00
-- url     : https://prove2.me/theorems/8c9d760e-7661-5204-8093-88acb66d397c
-- title:
--   Unit Det Root: alt E std H
-- statement:
--   The Unit Det Root construction uses the alt E std H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L60-L65

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.altE_stdH {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.altE (UnitDetRootDefs.stdH L m) x y = ∑ i, (x i * conj (y i)).im / UnitDetRootDefs.area L := by sorry
