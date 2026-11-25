-- Prove2me | Theorems.Thm_PI_LocCartanPair_pair_base_of_lag
-- name    : PI.LocCartanPair.pair_base_of_lag
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:24.522002+00:00
-- url     : https://prove2.me/theorems/fad99d2a-9737-485c-abc9-414b8e83fc8e
-- title:
--   Loc Cartan Pair: pair base of lag
-- statement:
--   The Loc Cartan Pair construction uses the pair base of lag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L122-L127

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]

theorem PI.LocCartanPair.pair_base_of_lag {ι : Type} [Fintype ι] [DecidableEq ι] (A e h h₁ : Matrix ι ι R) (c : R)
    (hh : h = c • h₁) (hh₁ : IsUnit h₁.det) (he : e * e = e) (heA : eᴴ * A = A * (1 - e)) :
    ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f := by sorry
