-- Prove2me | Theorems.Thm_PI_RWS_bidet_hom
-- name    : PI.RWS.bidet_hom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:02.145121+00:00
-- url     : https://prove2.me/theorems/7e070de8-7ba7-565c-9fe1-2fbe3dcd6006
-- title:
--   RWS: bidet hom
-- statement:
--   The RWS construction uses the bidet hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowWeightSpan/RowWtSpanOfBideterminant.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowWeightSpan/RowWtSpanOfBideterminant.lean#L44-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant
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
open PI PI.RWS
open PI.RW

theorem PI.RWS.bidet_hom {K : Type} [CommRing K] {k N : ℕ} (a : Fin k) (sz : Fin N → ℕ)
    (hsz : ∀ j, sz j ≤ k) (I : ∀ j, Fin (sz j) → Fin k) :
    IsWeightedHomogeneous (rowW a) (bideterminant K sz hsz I)
      (∑ j, (Finset.univ.filter fun p => I j p = a).card) := by sorry
