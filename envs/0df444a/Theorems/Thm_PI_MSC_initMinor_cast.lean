-- Prove2me | Theorems.Thm_PI_MSC_initMinor_cast
-- name    : PI.MSC.initMinor_cast
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:59.151507+00:00
-- url     : https://prove2.me/theorems/409acf59-84d0-4884-a5bc-4a3bdc946b2e
-- title:
--   MSC: init Minor cast
-- statement:
--   The MSC construction uses the init Minor cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L65-L69

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC

theorem PI.MSC.initMinor_cast (R : Type) [CommRing R] {r n s s' : ℕ} (h : s' = s) (I : Fin s → Fin r)
    (hs : s ≤ n) (hs' : s' ≤ n) :
    initMinor R (I ∘ Fin.cast h) hs' = initMinor R I hs := by sorry
