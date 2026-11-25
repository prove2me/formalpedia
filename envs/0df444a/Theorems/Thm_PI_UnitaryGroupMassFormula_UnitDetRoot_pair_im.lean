-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_pair_im
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.pair_im
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:41.672833+00:00
-- url     : https://prove2.me/theorems/eaefc25e-c378-4fcb-82b8-f864f32239cb
-- title:
--   Unit Det Root: pair im
-- statement:
--   The Unit Det Root construction uses the pair im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L45-L52

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
variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.pair_im (p q p' q' : ℤ) :
    ((lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d)) * conj (lam * ((p' : ℂ) * a + (q' : ℂ) * UnitDetRootDefs.cmTheta b d))).im
      = Complex.normSq lam * a * (Real.sqrt d / 2) * ((q * p' - p * q' : ℤ) : ℝ) := by sorry
