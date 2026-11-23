-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_Mb_mul_of
-- name    : PI.TwChrOne.Pf.Mb_mul_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:56.921874+00:00
-- url     : https://prove2.me/theorems/54079d8e-2b62-468d-854e-8783bdac8c1d
-- title:
--   Pf: Mb mul of
-- statement:
--   The Pf construction uses the Mb mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L211-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L211-L233

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}

theorem PI.TwChrOne.Pf.Mb_mul_of {r g h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hDA : ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0)
    (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i))
    (hgI : ∀ (j : ℕ) i, IntAt P (g (Loc.eN E (N + c) j) i))
    (hh : ∀ t : Fin (N - kj), h (Loc.eN E (N + c) (kj + t.1)) = r (g (Loc.eN E (N + c) (kj + t.1)))) :
    Mb P kj N c h = Mb P kj N c r * Mb P kj N c g := by sorry
