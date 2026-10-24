-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem13
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:03:21.163898+00:00
-- url     : https://prove2.me/theorems/a80f0e15-8904-410b-bc84-3a6c1e78c207
-- title:
--   Ordinary compression under the letterwise criterion
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. For each fixed $0<\lambda<1$, there exist $K>0,n_0$ such that every $n\ge n_0$, $n\ge1$, admits an ordinary visible stochastic code, with independent private randomness and no shared seed, whose output law $\widehat W_n(x)$ satisfies
--
--   $$
--   \log_2|C|\le nI+K\sqrt n,\qquad
--   \sum_x P^n(x)\frac1n\sum_{k=1}^n
--    d_{\rm TV}\bigl(W_{x_k},\widehat W_n(x)_k\bigr)\le\lambda.
--   $$
--   The subscript $k$ denotes the marginal on the $k$th output position. This is the source's letterwise criterion, with averaging outside the distance.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 7, Theorem 13

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 13, PDF p.7: no shared randomness and the precise letterwise criterion (5).
Communicating a choice from polynomially many seeds is included in the message alphabet. -/
theorem theorem13 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) (error : ℝ) (he : 0 < error) (he1 : error < 1) :
    ∃ k : ℝ, 0 < k ∧ ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∃ c : DistributionCompressionCode A B n,
        Real.logb 2 (c.size : ℝ) ≤ n * sourceInformationBits p w + k * Real.sqrt n ∧
        letterError p w c ≤ error := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
