-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_affineWeylAlcove
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.affineWeylAlcove
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:34:27.356993+00:00
-- url     : https://prove2.me/theorems/a9d4e3e1-edbe-4481-928a-31bd5933bcaa
-- title:
--   Affine Weyl closed fundamental domains
-- statement:
--   Let $N\ge2$, $\ell\ge1$, $L=N+\ell$, $\Lambda_0=L\{m\in\mathbb Z^N:\sum_i m_i=0\}$, and $W=\Lambda_0\rtimes S_N$ acting by translations and coordinate permutations on $\mathbb R^N$. Put
--
--   $$C=\{x:|x_i-x_j|\le L\ \forall i,j\},\qquad D=\{x:x_1\ge\cdots\ge x_N,\ x_1-x_N\le L\}.$$
--
--   The closed set $C$ is a fundamental domain for $\Lambda_0$, and $D$ is one for $W$: every orbit meets the respective domain and distinct translates have disjoint interiors. A point belongs to the $W$-orbit of $\operatorname{int}D$ exactly when its affine stabilizer is trivial. At every other point $x$, there is a transposition $\sigma\in S_N$ with $\sigma(x)-x\in\Lambda_0$.
--
--   The assertion allows repeated boundary representatives. Singularity is a congruence modulo the root lattice, not necessarily a transposition fixing the point itself.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 43, §34: Lemma

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §34 lemma, all three clauses, PDF p.43. Closed fundamental domains permit
boundary repetitions. The regular locus is the orbit of the open dominant
alcove; singular points admit a transposition modulo Λ₀. -/
theorem affineWeylAlcove (N ell : ℕ) (hN : 2 ≤ N) (hell : 1 ≤ ell) :
    IsTranslationFundamentalDomain ell (translationAlcove N ell) ∧
    IsAffineFundamentalDomain ell (dominantAlcove N ell) ∧
    ∀ x : Fin N → ℝ,
      (HasTrivialRealStabilizer ell x ↔
        ∃ (w : AffineWeylElement N) (y : Fin N → ℝ),
          y ∈ interior (dominantAlcove N ell) ∧ realAffineAction ell w y = x) ∧
      (¬HasTrivialRealStabilizer ell x →
        ∃ i j : Fin N, i ≠ j ∧ IsRealRootTranslation ell
          (fun a => x ((Equiv.swap i j).symm a) - x a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
