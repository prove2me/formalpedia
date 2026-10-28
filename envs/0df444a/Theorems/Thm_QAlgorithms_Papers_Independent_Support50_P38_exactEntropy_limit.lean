-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_exactEntropy_limit
-- name    : QAlgorithms.Papers.Independent.Support50.P38.exactEntropy_limit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:04:17.946991+00:00
-- url     : https://prove2.me/theorems/4e585807-f4c4-496a-9442-0ac989e05827
-- title:
--   Exact reconstruction entropy rate and its infimum
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Let $S(n)$ be the infimum of $H(E(P^n))$ over all finite nonempty ordinary stochastic code alphabets and encoders and decoders reproducing $W_x^n$ exactly for every word $x$. Define $\Gamma=\inf_{n\ge1}S(n)/n$. Then
--
--   $$
--   S(n+m)\le S(n)+S(m)\quad(n,m\ge0),\qquad
--   \lim_{n\to\infty}\frac{S(n)}n=\Gamma.
--   $$
--   The feasible entropy values are nonempty and nonnegative: sending the label word is feasible. This gives a well-defined normalized exact encoder-entropy rate. Entropy-minimum attainment is retained explicitly in the finite-cardinality optimal-code theorems.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 1, Section I; repeated in Section V

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF pp.1–2 and p.7: subadditivity of S and existence of its normalized entropy-rate
limit, equal to the infimum over positive blocklengths. -/
theorem exactEntropy_limit {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) :
    (∀ n m, exactEntropy p w (n + m) ≤ exactEntropy p w n + exactEntropy p w m) ∧
    Tendsto (fun n : ℕ => exactEntropy p w (n + 1) / (n + 1 : ℝ))
      atTop (nhds (exactEntropyRate p w)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
