-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_remark16
-- name    : QAlgorithms.Papers.Independent.Support50.P38.remark16
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:06:39.394299+00:00
-- url     : https://prove2.me/theorems/5896517a-874a-477b-a432-e0b08201483c
-- title:
--   Improved bound with entropy-minimum attainment
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Assume $c=|X|\ge2$ and $d=|Y|\ge2$. If $S(1)$ is the infimum of the message entropy of exact ordinary visible codes, there exists one attaining that infimum and satisfying
--
--   $$
--   D\circ E=W,\qquad H(E(P))=S(1),\qquad |C|\le cd-c+1.
--   $$
--   The bound refines the finite intermediate alphabet required for an entropy-optimal exact code.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 8, Remark 16

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Remark 16, PDF p.8: the improved finite alphabet bound still attains the entropy
minimum; C and D here are cardinalities, each at least two. -/
theorem remark16 {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (ha : 2 ≤ Fintype.card A) (hb : 2 ≤ Fintype.card B)
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w) :
    ∃ c : DistributionCompressionCode A B 1, c.Exact w ∧
      shannon (c.messageLaw p) = exactEntropy p w 1 ∧
      c.size ≤ Fintype.card A * Fintype.card B - Fintype.card A + 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
