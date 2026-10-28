-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_commonRandomness_reversal
-- name    : QAlgorithms.Papers.Independent.Support50.P38.commonRandomness_reversal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:07:20.753996+00:00
-- url     : https://prove2.me/theorems/8611d8de-bfd0-478e-a764-650c459d8cef
-- title:
--   Conditional common-randomness generation without communication
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Assume the global assertion of Question 4: for every finite source and channel and each $0<\lambda<1$, ordinary minimum code rates converge to mutual information. For every $\epsilon,\alpha>0$, all sufficiently large positive $n$ admit a positive integer $N$ and normalized local stochastic kernels $A_\nu$ on $X^n$ and $B_\nu$ on $Y^n$ with
--
--   $$
--   \frac{\log_2N}{n}\le I+\alpha,\qquad
--    d_{\rm TV}\left(G_n,\frac1N\sum_{\nu=1}^N A_\nu\otimes B_\nu\right)\le\epsilon,
--   $$
--   where $G_n(x,y)=P^n(x)W^n(y|x)$. A uniform shared seed selects $\nu$; the local outputs are independent conditional on it, with no communication. The result is an implication from an open assertion, not an unconditional reversibility theorem.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 8, Section VI.A

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF pp.8–9: CONDITIONAL reversal of common-randomness extraction. Question 4 is
an antecedent, never an available theorem. The two local randomizations are independent
given a single uniform shared seed, and no public discussion is allowed. -/
theorem commonRandomness_reversal (hquestion : QuestionFour)
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error slack : ℝ) (he : 0 < error) (hs : 0 < slack) :
    ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∃ seeds : ℕ, 0 < seeds ∧ Real.logb 2 (seeds : ℝ) / n ≤ sourceInformationBits p w + slack ∧
        ∃ (a : Fin seeds → SourceWord A n → ℝ) (b : Fin seeds → SourceWord B n → ℝ),
          IsStochastic a ∧ IsStochastic b ∧
          tv (jointWordLaw p w) (generatedPairs a b) ≤ error := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
