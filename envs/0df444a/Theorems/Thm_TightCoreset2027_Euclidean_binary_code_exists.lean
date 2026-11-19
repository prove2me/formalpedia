-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_binary_code_exists
-- name    : TightCoreset2027.Euclidean.binary_code_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:59:00.075107+00:00
-- url     : https://prove2.me/theorems/231ea627-5cb8-4a70-bbad-c1b52eb282a4
-- title:
--   Binary words with no four-word zero sum
-- statement:
--   Let $L,q$ be nonnegative integers satisfying $q+\binom q3<2^L$. There is a set $S\subseteq\mathbb F_2^L$ such that
--
--   $$|S|=q,\qquad \sum_{b\in T}b\ne0\quad\text{whenever }T\subseteq S\text{ and }|T|=4.$$
--
--   Addition is coordinatewise modulo two. This is the coding component of Lemma 2.1, providing distinct words and the even-parity cancellations used in its fourth-moment argument. The statement also includes the empty-set case, for which the same construction is valid.
-- source:
--   Hu–Huang–Li–Xu, Tight Coreset Bounds for (k,z)-Clustering in Euclidean and Doubling Metrics, STOC 2027 submission #879, §2.4, proof of Lemma 2.1, first paragraph, printed p. 16 / PDF p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean
 theorem binary_code_exists (L q : ℕ) (hcode : q + Nat.choose q 3 < 2 ^ L) :
    ∃ S : Finset (Fin L → ZMod 2), S.card = q ∧
      ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0 := by sorry
end TightCoreset2027.Euclidean
