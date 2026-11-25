-- Prove2me | Theorems.Thm_PI_WwCauchyBinetWork_factor_expand
-- name    : PI.WwCauchyBinetWork.factor_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:38.332474+00:00
-- url     : https://prove2.me/theorems/7043fc8e-2a93-41a4-b712-8335672a982f
-- title:
--   Ww Cauchy Binet Work: factor expand
-- statement:
--   The Ww Cauchy Binet Work construction uses the factor expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CauchyBinet/WwCauchyBinetMain.lean#L17-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CauchyBinet/WwCauchyBinetMain.lean#L17-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.WwCauchyBinetWork
open PI.WwCauchyBinet

theorem PI.WwCauchyBinetWork.factor_expand {Lt k : Type} [CommRing k] (N : ℕ) (s : Lt) (h : ℕ) (y : Fin N → ℕ → k) :
    Matrix.det (Matrix.of fun i j : Fin h =>
      ∑ a : Fin N, MvPolynomial.C (y a (j : ℕ)) * (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k))
    = ∑ I : Fin h ↪o Fin N,
        MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => y (I i) (j : ℕ))) *
        MvPolynomial.map (Int.castRingHom k) (Matrix.det (Matrix.of fun i j : Fin h =>
          (MvPolynomial.X (s, (i : ℕ), I j) : MvPolynomial (Lt × ℕ × Fin N) ℤ))) := by sorry
