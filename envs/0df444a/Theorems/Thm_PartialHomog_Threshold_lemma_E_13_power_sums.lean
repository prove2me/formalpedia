-- Prove2me | Theorems.Thm_PartialHomog_Threshold_lemma_E_13_power_sums
-- name    : PartialHomog.Threshold.lemma_E_13_power_sums
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:26:30.563281+00:00
-- url     : https://prove2.me/theorems/7de2f97a-0c88-4b42-8712-521becd1840d
-- title:
--   Proof of Lemma E.13 — Newton's identities, and power sums of orders $1,\dots,M \ge n$ determine a multiset of $n$ reals
-- statement:
--   (1) **Newton's identities.** In a commutative ring $S$, let $x=(x_1,\dots,x_n)$ and $y=(y_1,\dots,y_n)$ have equal elementary symmetric functions $e_k(x)=e_k(y)$ for $1\le k\le M$. Then their power sums agree:
--   $$\sum_j x_j^p=\sum_j y_j^p\qquad(1\le p\le M).$$
--   (2) Let $x,y\in\mathbb R^n$ with $n\le M$ and $\sum_jx_j^p=\sum_jy_j^p$ for $1\le p\le M$. Then $\{x_1,\dots,x_n\}=\{y_1,\dots,y_n\}$ as multisets.
--
--   In the proof of Lemma E.13, (1) is applied to the rational functions $c_{ij}/\ell_j$ with $M=D-3$, and (2) to the multisets $\{c_{ij}/\alpha_j\}_{j\in G}$, $|G|\le D-3$.
--
--   **Formalization Note** Families are indexed by `Fin n`; $e_k$ is `Multiset.esymm` of the multiset `univ.val.map x`; multiset equality is `univ.val.map x = univ.val.map y`.
--
--   Differences from the source:
--   - generalization: Newton's identities applied to rational functions c_ij/ℓ_j over ℝ (the field ℝ(z)) → any commutative ring S; reason: Newton's identities express p_k as an integer polynomial in e_1, …, e_k; S = FractionRing ℝ[z] is the source's case
--   - encoding: the multiset {c_ij/α_j}_{j∈G} and |G| ≤ D − 3 power sums → families `Fin n → ℝ` with n ≤ M and orders 1 ≤ p ≤ M; reason: relabelling: n = |G|, M = D − 3
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 27 (PDF 29), proof of Lemma E.13

import Mathlib

namespace PartialHomog.Threshold

/-- Proof of Lemma E.13 (p. 27): (1) Newton's identities: in a commutative ring, if two families
`x, y` of `n` elements have equal elementary symmetric functions of every degree `1 ≤ k ≤ M`,
they have equal power sums of every order `1 ≤ p ≤ M`; (2) two families of `n ≤ M` real
numbers with equal power sums of every order `1 ≤ p ≤ M` are equal as multisets. -/
theorem lemma_E_13_power_sums {S : Type*} [CommRing S] :
    (∀ (n M : ℕ) (x y : Fin n → S),
      (∀ k, 1 ≤ k → k ≤ M →
        (Finset.univ.val.map x).esymm k = (Finset.univ.val.map y).esymm k) →
      ∀ p, 1 ≤ p → p ≤ M → ∑ j, x j ^ p = ∑ j, y j ^ p) ∧
    (∀ (n M : ℕ) (x y : Fin n → ℝ), n ≤ M →
      (∀ p, 1 ≤ p → p ≤ M → ∑ j, x j ^ p = ∑ j, y j ^ p) →
      Finset.univ.val.map x = Finset.univ.val.map y) := by sorry

end PartialHomog.Threshold
