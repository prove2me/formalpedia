-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_remark10
-- name    : QAlgorithms.Papers.Independent.Support50.P38.remark10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:01:02.936683+00:00
-- url     : https://prove2.me/theorems/fd714849-4016-48b5-bcc0-55d1c747e02a
-- title:
--   Small-error communication refinement with passive feedback
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Fix a typical width $\delta>0$. There are $K>0$ and $n_0$, independent of the error parameter, such that for every $0<\lambda\le1/2$ and $n\ge n_0$, $n\ge1$, a uniform-shared-seed visible code satisfies
--
--   $$
--   \log_2|C|\le nI+K(-\log_2\lambda)\sqrt n.
--   $$
--   Its seed-averaged block error is at most $\lambda$, and its pointwise error is at most $\lambda$ on $T^n_{P,\delta}$, defined by the count tolerance $\delta\sqrt{nP(a)(1-P(a))}$. Moreover, the decoder's output word is a deterministic function of the seed and message, so both parties recover the identical realized word. This refines the error dependence of the communication bound; no additional error-dependent seed-size bound is asserted.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 5, Remark 10

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Remark 10, PDF p.5: quantitative small-error refinement and noiseless passive feedback.
The constant and threshold are uniform in 0 < lambda <= 1/2; no lambda-dependent seed bound
is invented. The source's supporting tail (10) has a counterexample (see moderation ledger);
this statement retains the expressly stated resource claim without assuming that tail. -/
theorem remark10 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) (width : ℝ) (hd : 0 < width) :
    ∃ k : ℝ, 0 < k ∧ ∃ threshold : ℕ,
      ∀ error : ℝ, 0 < error → error ≤ 1 / 2 → ∀ n ≥ threshold, 0 < n →
        ∃ c : SharedCode A B n, c.Uniform ∧ c.PassiveFeedback ∧
          Real.logb 2 (c.size : ℝ) ≤
            n * sourceInformationBits p w + k * (-Real.logb 2 error) * Real.sqrt n ∧
          sourceAverageBlockError p w c.output ≤ error ∧
          ∀ x, VarianceTypicalWord p width x → tv (wordChannel w x) (c.output x) ≤ error := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
