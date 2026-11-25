-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_good_prod
-- name    : PI.OddDualWeyl.Hom.good_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:04.186489+00:00
-- url     : https://prove2.me/theorems/27a3f797-8bac-5fb2-a86b-9269c14a4eb6
-- title:
--   Hom: good prod
-- statement:
--   The Hom construction uses the good prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L79-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem PI.OddDualWeyl.Hom.good_prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial (Fin k × Fin k) R))
    (d : ι → ℤ) (h : ∀ i ∈ s, Good wt δ (d i) (p i)) : Good wt δ (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by sorry
