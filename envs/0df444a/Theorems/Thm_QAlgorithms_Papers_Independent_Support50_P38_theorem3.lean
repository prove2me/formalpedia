-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem3
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:56:57.83013+00:00
-- url     : https://prove2.me/theorems/2dfc286f-e522-4a90-9aef-b75eaa33d443
-- title:
--   Classical fixed-error strong converse
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Let $M(n,\lambda)$ be the minimum message alphabet cardinality of an ordinary visible stochastic encoder and decoder, with independent private randomness and $P^n$-average block total variation at most $\lambda$. For every fixed $0<\lambda<1$,
--
--   $$
--   \liminf_{n\to\infty}\frac{\log_2 M(n,\lambda)}n\ge I.
--   $$
--   This is a strong converse lower bound; it does not assert achievability or existence of a limit.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 3, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 3, PDF p.3: fixed-error strong converse without common randomness.
The liminf is retained; no equality or existence of a limit is asserted. -/
theorem theorem3 {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error : ℝ) (he : 0 < error) (he1 : error < 1) :
    sourceInformationBits p w ≤ Filter.liminf (sizeRate p w error) atTop := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
