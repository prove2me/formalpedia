-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_5
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:09.432834+00:00
-- url     : https://prove2.me/theorems/e766f29c-fa75-43dd-a70c-2cbb6f6594c2
-- title:
--   Lemma 6.5 — Dense random sumset bound on arbitrary available positions
-- statement:
--   Let $n\ge0$, $B\subseteq\{0,\ldots,n-1\}$, $0<\eta\le1$ and integer $u\ge1$ with $u\eta\le1/4$. Include each element of B independently in T with probability η, and put $\mu=\eta|B|$. Then
--   $$\Pr_T[\exists A\subseteq\{0,\ldots,n-1\},\ |A|\le u,\ |A+T|<|A||T|/2]\le e^{-\mu/12}+(n+1)^u e^{-\mu/128}.$$
--   Sumsets use ordinary integer addition and A,B may be empty, including the empty interval at n=0. This is a simultaneous sumset bound without a sparseness assumption; exp denotes the natural exponential.
--
--   Differences from the source:
--   - encoding: integer-position sumsets and independent Bernoulli subsets → natural-coordinate Finsets and the explicit product law; reason: nonnegative integer addition preserves exactly these sumsets and their cardinalities
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.5, printed p.28 / PDF p.30

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_SeedAndSubset

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.5: product sampling on arbitrary available positions, no sparse-set assumption. -/
theorem lemma_6_5 (n : ℕ) (B : Finset ℕ)
    (hB : B ⊆ Finset.range n) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (u : ℕ) (hu : 1 ≤ u) (huη : (u : ℝ)*η ≤ 1/4) :
  subsetProb B η (fun T => ∃ A : Finset ℕ, A ⊆ Finset.range n ∧ A.card ≤ u ∧
    ((sumset A T).card : ℝ) < (A.card : ℝ)*T.card/2) ≤
    Real.exp (-(η*B.card)/12) + (n+1 : ℝ)^u * Real.exp (-(η*B.card)/128) := by sorry

end ParityBarrier563.Trilinear.Supplement
