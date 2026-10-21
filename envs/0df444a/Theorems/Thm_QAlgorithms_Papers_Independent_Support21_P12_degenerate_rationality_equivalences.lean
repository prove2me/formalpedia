-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_degenerate_rationality_equivalences
-- name    : QAlgorithms.Papers.Independent.Support21.P12.degenerate_rationality_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:13:57.393674+00:00
-- url     : https://prove2.me/theorems/e7d7117e-c717-4fd0-91f0-755e9472c402
-- title:
--   Five equivalent rationality conditions in all characteristics
-- statement:
--   Let $F$ be algebraically closed and $n\ge2$. Let $\widehat N_{n,F}$ be the actual degenerate affine BMW algebra with parameters $\Omega=(\omega_a)_{a\ge0}$ and suppose $e_1\ne0$ in this algebra. The following are equivalent:
--
--   1. The formal series $\sum_{a\ge0}\omega_at^{-a}$ is rational.
--   2. There exist $r>0$, $N\ge0$, and $a_0,\ldots,a_{r-1}\in F$ for which the recurrence below holds for every $\ell\ge N$.
--   3. Such a positive-order monic recurrence holds for every $\ell\ge0$.
--   4. Some positive-degree root tuple is admissible in the actual two-strand cyclotomic quotient.
--   5. The affine algebra has a finite dimensional module on which $e_1$ acts nontrivially.
--
--   $$\omega_{r+\ell}+\sum_{j=0}^{r-1}a_j\omega_{j+\ell}=0.$$
--
--   The field may have characteristic two. Rationality is formal: with $z=t^{-1}$, the series is a quotient of polynomials with denominator nonzero at zero. The theorem relates the parameter sequence to genuine cyclotomic quotients and finite modules.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 18, Theorem 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Theorem 7.1, ALL FIVE equivalent conditions, PDF pp.18--19. Eventual
and everywhere recurrences retain their different thresholds; characteristic
2 is included. The e_1≠0 hypothesis is on the actual affine presentation. -/
theorem degenerate_rationality_equivalences (F : Type*) [Field F] [IsAlgClosed F]
    (omega : ℕ → F) (n : ℕ) (hn : 2 ≤ n)
    (he : ae F omega .degenerate n 0 ≠ 0) :
    (RationalSequence omega ↔ ∃ N : ℕ, RecurrenceFrom omega N) ∧
    ((∃ N : ℕ, RecurrenceFrom omega N) ↔ RecurrenceFrom omega 0) ∧
    (RecurrenceFrom omega 0 ↔ HasAdmissibleRoots F omega .degenerate) ∧
    (HasAdmissibleRoots F omega .degenerate ↔ HasFiniteModule (F := F) (ae F omega .degenerate n 0)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
