-- Prove2me | Theorems.Thm_PI_OpWords_xdeg_of_bihom
-- name    : PI.OpWords.xdeg_of_bihom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:44.771633+00:00
-- url     : https://prove2.me/theorems/1aabb79f-a3d5-48d2-89fb-ea193d39d106
-- title:
--   Op Words: xdeg of bihom
-- statement:
--   The Op Words construction uses the xdeg of bihom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L18-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.xdeg_of_bihom {d : ℕ} {g : Pol K k} (hg : g ∈ Bihom K k d) {m : Fin k ⊕ Fin k →₀ ℕ}
    (hm : m ∈ g.support) : ∑ a, m (Sum.inl a) = d := by sorry
