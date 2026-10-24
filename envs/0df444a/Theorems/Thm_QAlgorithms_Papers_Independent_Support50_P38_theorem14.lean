-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem14
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:05:17.544605+00:00
-- url     : https://prove2.me/theorems/f5e32328-be57-4364-86fa-de38066056c4
-- title:
--   Ordinary compression rate bounded by exact encoder entropy
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Let $M(n,\lambda)$ denote the minimum ordinary visible code alphabet cardinality at $P^n$-average block total variation at most $\lambda$. Let $S(k)$ be the optimized entropy of the encoder's message under exact reconstruction, and $\Gamma=\inf_{k\ge1}S(k)/k$. For every fixed $0<\lambda<1$,
--
--   $$
--   \limsup_{n\to\infty}\frac{\log_2 M(n,\lambda)}n\le\Gamma.
--   $$
--   This is an upper bound through exact encoder entropy, rather than through exact code cardinality.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 7, Theorem 14

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 14, PDF p.7: the ordinary fixed-error limsup rate is at most the optimized
exact encoder-entropy rate Gamma. Blocking the argument with arbitrary superletters is
implicit in the source; Gamma is not the minimum exact log-cardinality rate. -/
theorem theorem14 {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error : ℝ) (he : 0 < error) (he1 : error < 1) :
    Filter.limsup (sizeRate p w error) atTop ≤ exactEntropyRate p w := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
