-- Prove2me | Theorems.Thm_PI_DvRows_neg_vAdd_le
-- name    : PI.DvRows.neg_vAdd_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:40.753011+00:00
-- url     : https://prove2.me/theorems/ffaf561b-30d3-4412-ab2b-199ea6a3ce35
-- title:
--   Dv Rows: neg v Add le
-- statement:
--   The Dv Rows construction uses the neg v Add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L12-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.DvRows.neg_vAdd_le (w : HeightOneSpectrum (𝓞 K)) (x c : K) (hc : c ≠ 0)
    (hci : w.valuation K c ≤ 1) (d : ℕ) (h : w.valuation K x * (w.valuation K c) ^ d ≤ 1) :
    -vAdd w x ≤ (d : ℤ) * vAdd w c := by sorry
