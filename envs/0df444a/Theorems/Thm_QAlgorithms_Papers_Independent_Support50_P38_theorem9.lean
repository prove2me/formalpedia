-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem9
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:56:10.566312+00:00
-- url     : https://prove2.me/theorems/f49c571a-8737-46f9-b389-7139327c209a
-- title:
--   Common-randomness compression with typical-word guarantees
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Fix $0<\lambda<1$ and $\delta>0$. There are $K>0$ and $n_0$, depending only on these fixed data, such that every $n\ge n_0$, $n\ge1$, admits a visible stochastic code with common message alphabet $C$ and an independent uniform seed on $N$ values. If $\widehat W_n$ is its output channel averaged over the seed, then
--
--   $$
--   \log_2|C|\le nI+K\sqrt n,\qquad \log_2N\le nH(W|P)+K\sqrt n,
--   $$
--   $$
--   \sum_x P^n(x)d_{\rm TV}(W_x^n,\widehat W_n(x))\le\lambda,\qquad
--   \forall x\in T^n_{P,\delta},\quad d_{\rm TV}(W_x^n,\widehat W_n(x))\le\lambda.
--   $$
--   Here $T^n_{P,\delta}$ consists of words whose count of each letter $a$ differs from $nP(a)$ by at most $\delta\sqrt{nP(a)(1-P(a))}$. The result quantifies communication and shared randomness separately.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 4, Theorem 9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 9, PDF pp.4–5, including (4), (11), and BOTH resource bounds. The general
construction is credited by the source to Bennett et al. [6], footnote 4, and independently
Duer–Vidal–Cirac [9]. Constants may depend on the fixed source, error, and typical width. -/
theorem theorem9 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) (error width : ℝ)
    (he : 0 < error) (he1 : error < 1) (hd : 0 < width) :
    ∃ k : ℝ, 0 < k ∧ ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∃ c : SharedCode A B n, c.Uniform ∧
        Real.logb 2 (c.size : ℝ) ≤ n * sourceInformationBits p w + k * Real.sqrt n ∧
        Real.logb 2 (c.seeds : ℝ) ≤ n * sourceConditionalEntropyBits p w + k * Real.sqrt n ∧
        sourceAverageBlockError p w c.output ≤ error ∧
        ∀ x, VarianceTypicalWord p width x → tv (wordChannel w x) (c.output x) ≤ error := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
