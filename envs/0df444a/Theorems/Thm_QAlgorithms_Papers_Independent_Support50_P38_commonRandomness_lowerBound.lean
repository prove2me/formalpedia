-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_commonRandomness_lowerBound
-- name    : QAlgorithms.Papers.Independent.Support50.P38.commonRandomness_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:58:35.526991+00:00
-- url     : https://prove2.me/theorems/685d51b1-3eae-4626-a677-b8e0b4b24b24
-- title:
--   Weak converse with independent shared randomness
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. For each fixed pair of alphabets there is a single function $\widetilde f:(0,1)\to\mathbb R$, uniform over all normalized source laws $P$ and stochastic channels $W$ on those alphabets, with $\widetilde f(\lambda)\to0$ as $\lambda\downarrow0$, such that every positive blocklength, every $0<\lambda<1$, and every visible code with an independent shared seed of arbitrary law and seed-averaged block error at most $\lambda$ satisfy
--
--   $$
--   \log_2|C|\ge n\bigl(I-\widetilde f(\lambda)\bigr).
--   $$
--   This preserves the weak information lower bound when common randomness is allowed, without assigning the correction function an unsupported formula.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 3, Unnumbered extension of Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–4: the weak converse still holds for arbitrary independent shared seed laws.
The vanishing correction f-tilde is uniform over source laws and channels on the fixed
alphabets, as in the entropy-continuity bound f to which the source refers. -/
theorem commonRandomness_lowerBound {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    ∃ f : ℝ → ℝ, Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (p : A → ℝ) (w : A → B → ℝ), IsLaw p → IsStochastic w →
        ∀ error : ℝ, 0 < error → error < 1 → ∀ n : ℕ, 0 < n →
          ∀ c : SharedCode A B n, sourceAverageBlockError p w c.output ≤ error →
            n * (sourceInformationBits p w - f error) ≤ Real.logb 2 (c.size : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
