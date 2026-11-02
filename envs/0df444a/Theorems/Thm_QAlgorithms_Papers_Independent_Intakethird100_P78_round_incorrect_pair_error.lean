-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_round_incorrect_pair_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.round_incorrect_pair_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:15:31.381617+00:00
-- url     : https://prove2.me/theorems/82b8edaa-6641-456f-a1c1-33f2af3453cc
-- title:
--   One round from a fixed incorrect pair has error exactly two over d
-- statement:
--   Let $d>2$ and let $f$ be the target permutation at a fixed input pair. Fix starting labels $(\hat a,\hat b)$ with $f(\hat a)\ne\hat b$. Draw a fresh shared coin, independently of an exact copy of the corrected smaller resource from Lemma 1. With probability $1/d$ retain the starting pair; otherwise query the resource at the augmented local inputs and relabel its two outputs with $r_{\hat a}$ and $r_{\hat b}$.
--
--   If $(A,B)$ is the resulting pair, then
--
--   $$
--   \Pr[f(A)\ne B\mid\hat a,\hat b]=\frac{2}{d}.
--   $$
--
--   The equality describes the error of a single round conditioned on its fixed initial pair. It uses the disclosed correction to equation (7), whose independent moderation is pending.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 6, Lemma 2: one round from an incorrect pair has error probability 2/d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Lemma 2: conditional on a fixed incorrect initial pair, the
round's mismatch probability equals 2/d. This uses corrected (7), as
disclosed above; it does not assume the conclusion that Dprime is a permutation.
Independent source-correction moderation is pending. -/
theorem round_incorrect_pair_error
    {m : ℕ} (hm : 1 < m) (f : Equiv.Perm (Fin (m + 1)))
    (ahat bhat : Fin (m + 1)) (hbad : f ahat ≠ bhat) :
    (∑ a, ∑ b, if f a ≠ b then
      roundKernel (lt_trans Nat.zero_lt_one hm) f ahat bhat a b else 0) =
        2 / ((m + 1 : ℕ) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
