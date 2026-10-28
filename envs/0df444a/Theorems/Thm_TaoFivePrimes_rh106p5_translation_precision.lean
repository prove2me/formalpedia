-- Prove2me | Theorems.Thm_TaoFivePrimes_rh106p5_translation_precision
-- name    : TaoFivePrimes.rh106p5_translation_precision
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:11:36.918949+00:00
-- url     : https://prove2.me/theorems/3f364db0-c199-4147-be3d-fef41efda6da
-- title:
--   Tiered exact coefficient precision at height 106.5
-- statement:
--   Let $N_n/Q$ be the exact translated moment coefficient at height $106.5$ and $c_n/10^8$ its stored rounded value, with $Q>0$ as in the published translation arithmetic. Then, for $0\le n<40$,
--
--   $$
--   \left|\frac{N_n}{Q}-\frac{c_n}{10^8}\right|\le
--   \begin{cases}
--   10^{-8},&0\le n<20,\\
--   10^{-11},&20\le n<25,\\
--   10^{-16},&25\le n<30,\\
--   10^{-20},&30\le n<40.
--   \end{cases}
--   $$
--
--   These sharper exact bounds for the higher coefficients allow the same local xi polynomial to be used on a larger disk than a uniform rounding estimate permits.
--
--   **Formalization Note** The statement clears denominators and records the four bounds as integer inequalities.
-- source:
--   New tiered exact inequalities for the published height-106.5 translated coefficients, computed from TaoFivePrimes_RH14To100RoundedMomentData using RHLocalTranslationArithmetic. Existing moment data and method by sometik179, with theta/Mellin foundations by Gabewhigham. Related finite zero verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RH101To102TranslationCertificate
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh106p5_translation_precision : ∀ n : Fin 40,
    (if n.val < 20 then (1:ℤ) else if n.val < 25 then 1000
      else if n.val < 30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RHLocalTranslationArithmetic.numerator 213 (10^35) n.val-
        (TaoFivePrimes_RH106To107RoundedCoefficients.getD n.val 0)*
          (RHLocalTranslationArithmetic.denominator:ℤ)| ≤
            (RHLocalTranslationArithmetic.denominator:ℤ) := by sorry
