-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_round_correct_pair_distribution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.round_correct_pair_distribution
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:16:13.249453+00:00
-- url     : https://prove2.me/theorems/ba7dae8a-3f79-4c01-984a-e1cd7079a7c2
-- title:
--   One round from a correct pair reproduces the full target law
-- statement:
--   Let $d>2$, let $f$ be the target permutation at fixed inputs, and fix $(\hat a,\hat b)$ satisfying $f(\hat a)=\hat b$. Run the same one-round protocol with an independent shared coin of retention probability $1/d$ and an exact corrected smaller resource. Then, for every $a,b\in[d]$,
--
--   $$
--   \Pr[A=a,B=b\mid\hat a,\hat b]=\begin{cases}1/d,&f(a)=b,\\0,&f(a)\ne b.\end{cases}
--   $$
--
--   Thus one correct starting pair produces the full uniform graph distribution, including its uniform marginals. This result uses the disclosed correction to equation (7); independent moderation remains pending.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 6, Lemma 3: one round from a correct pair reproduces the full target law

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6–7, Lemma 3: a fixed correct starting pair gives the full
uniform target law in one round, not merely a matching pair almost surely.
Uses the corrected deletion-and-splicing construction (7).
Independent source-correction moderation is pending. -/
theorem round_correct_pair_distribution
    {m : ℕ} (hm : 1 < m) (f : Equiv.Perm (Fin (m + 1)))
    (ahat bhat : Fin (m + 1)) (hgood : f ahat = bhat) :
    ∀ a b, roundKernel (lt_trans Nat.zero_lt_one hm) f ahat bhat a b =
      (if f a = b then 1 / ((m + 1 : ℕ) : ℝ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
