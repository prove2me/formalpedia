-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem11
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:01:46.24005+00:00
-- url     : https://prove2.me/theorems/77da5912-1fae-47f6-a24a-2016e5cd01b1
-- title:
--   Two resource lower bounds for passive-feedback simulation
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Fix $0<\lambda<1$. There are $K>0,n_0$, depending only on the fixed source and error, such that for every $n\ge n_0$, $n\ge1$, and every code of block error at most $\lambda$ whose independent seed has an arbitrary law on $N$ values and whose output word is determined by seed and message, both bounds hold for that same code:
--
--   $$
--   \log_2|C|\ge nI-K\sqrt n,\qquad
--   \log_2(N|C|)\ge nH(PW)-K\sqrt n.
--   $$
--   The second bound constrains combined resources, and becomes a lower bound on randomness alone only after fixing the communication rate.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 5, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 11, PDF pp.5–6: both lower bounds hold for the SAME feedback code, even
for nonuniform independent seed laws. The positive exponential signs are those in the
printed theorem; the opposite sign in the final proof line on p.6 is a source typo. -/
theorem theorem11 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) (error : ℝ) (he : 0 < error) (he1 : error < 1) :
    ∃ k : ℝ, 0 < k ∧ ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∀ c : SharedCode A B n, c.PassiveFeedback → sourceAverageBlockError p w c.output ≤ error →
        n * sourceInformationBits p w - k * Real.sqrt n ≤ Real.logb 2 (c.size : ℝ) ∧
        n * shannon (sourceOutputMarginal p w) - k * Real.sqrt n ≤
          Real.logb 2 ((c.seeds : ℝ) * c.size) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
