-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem15
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:05:55.547992+00:00
-- url     : https://prove2.me/theorems/cc72a950-f6f2-476e-9791-b089a3d1e9b2
-- title:
--   Optimal exact code with bounded intermediate alphabet
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Put $c=|X|$ and $d=|Y|$, and let $S(1)$ be the infimum of encoder-message entropy over exact ordinary visible codes for $W$. There exists such a code $(E,D)$ attaining the infimum and obeying
--
--   $$
--   D\circ E=W,\qquad H(E(P))=S(1),\qquad |C|\le\max\{1,cd-1\}.
--   $$
--   This supplies both optimality attainment and a finite intermediate-alphabet bound.
--
--   **Source correction.** The printed bound is $cd-1$. At $c=d=1$ it is zero, although a normalized code needs one symbol. The corrected bound changes only that singleton corner.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 8, Theorem 15

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 15, PDF p.8: attainment of minimum encoder entropy with bounded cardinality.
SOURCE CORRECTION: printed CD-1 is replaced by max(1,CD-1), since C=D=1 requires one
normalized message symbol. Every nonsingleton printed bound is retained. -/
theorem theorem15 {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w) :
    ∃ c : DistributionCompressionCode A B 1, c.Exact w ∧
      shannon (c.messageLaw p) = exactEntropy p w 1 ∧
      c.size ≤ max 1 (Fintype.card A * Fintype.card B - 1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
