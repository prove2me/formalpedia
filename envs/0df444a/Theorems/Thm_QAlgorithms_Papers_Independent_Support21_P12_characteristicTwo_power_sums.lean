-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_characteristicTwo_power_sums
-- name    : QAlgorithms.Papers.Independent.Support21.P12.characteristicTwo_power_sums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:15:18.124378+00:00
-- url     : https://prove2.me/theorems/a2bd8169-5571-4ce7-bef5-ed36474c2143
-- title:
--   Recurrent Frobenius-compatible sequences are distinct-root power sums
-- statement:
--   Let $F$ be an algebraically closed field of characteristic two, and let $\Omega=(\omega_a)_{a\ge0}$ satisfy some monic constant-coefficient recurrence of positive order for all sufficiently large shifts. Suppose also $\omega_{2a}=\omega_a^2$ for every $a\ge0$. There exist an integer $d\ge0$ and pairwise distinct $u_1,\ldots,u_d\in F$ such that
--
--   $$\omega_a=\sum_{i=1}^d u_i^a\quad(a\ge1),\qquad \omega_0\in\{0,1\}.$$
--
--   The empty root list is allowed. The power-sum identity is restricted to positive indices; the constant coefficient is specified separately. This supplies a characteristic-two parameter description compatible with the integral eta polynomials.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 18, Lemma 7.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Lemma 7.3, PDF p.18. The number d may be zero; roots are pairwise distinct.
The positive-degree power-sum formula does not replace the separate omega_0 clause. -/
theorem characteristicTwo_power_sums (F : Type*) [Field F] [IsAlgClosed F] [CharP F 2]
    (omega : ℕ → F) (hrec : ∃ N : ℕ, RecurrenceFrom omega N)
    (hfrob : ∀ a : ℕ, omega (2*a) = omega a ^ 2) :
    ∃ (d : ℕ) (u : Fin d → F), Function.Injective u ∧
      (∀ a : ℕ, 1 ≤ a → omega a = ∑ i : Fin d, u i ^ a) ∧
      (omega 0 = 0 ∨ omega 0 = 1) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
