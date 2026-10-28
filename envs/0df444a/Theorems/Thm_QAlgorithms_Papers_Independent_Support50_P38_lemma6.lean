-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_lemma6
-- name    : QAlgorithms.Papers.Independent.Support50.P38.lemma6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:59:20.23578+00:00
-- url     : https://prove2.me/theorems/f05fc8b1-d83e-4edd-8fbd-6874dd34de3c
-- title:
--   Uniform exact-type channels and Bayes transpose
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $P$ a probability law on $X$, and $W:X\to\mathcal P(Y)$ a stochastic channel. All logarithms and entropies are in bits. Write $P^n,W^n$ for the memoryless product laws, $I=H(PW)-H(W|P)$, and $d_{\rm TV}(p,q)=\frac12\sum|p-q|$. Let $n\ge1$ and let $T$ be a joint exact $n$-type with marginals $R,S$. Write $\mathcal T_R,\mathcal T_S,\mathcal T_T$ for its type classes, $\mathcal T_T(x)$ and $\mathcal T_T(y)$ for its forward and reverse fibers, and $u_R,u_S$ for the uniform type laws. Define $W_T(y|x)=\mathbf1_T(x,y)/|\mathcal T_T(x)|$ and $V_T(x|y)=\mathbf1_T(x,y)/|\mathcal T_T(y)|$. Then
--
--   $$
--   u_RW_T=u_S,\qquad u_R(x)W_T(y|x)=u_S(y)V_T(x|y).
--   $$
--   For compatible $(x,y)$,
--
--   $$
--   W_T(y|x)=\frac{|\mathcal T_R|}{|\mathcal T_T|},\qquad
--   V_T(x|y)=\frac{|\mathcal T_S|}{|\mathcal T_T|}.
--   $$
--   On positive conditioning events, $u_R(x)=P^n(x)/P^n(\mathcal T_R)$, $u_S(y)=Q^n(y)/Q^n(\mathcal T_S)$ with $Q=PW$, and $W_T,V_T$ are the respective restrictions and normalizations of $W^n,V^n$, where $V$ is the Bayes transpose of $W$ under $P$. These identities establish the uniform-output and transpose structure used by the sampling construction.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 4, Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Lemma 6, PDF p.4: uniform type identities, forward and reverse cardinality ratios,
Bayes balance, and the conditional product-law identities on positive-mass events.
No full-support assumption is imposed. R and S are constructed as marginals of T. -/
theorem lemma6 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] {n : ℕ} (hn : 0 < n)
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (t : ExactType (A × B) n) :
    (∀ y, (∑ x, typeUniform t.left x * typeForward t x y) = typeUniform t.right y) ∧
    (∀ x y, typeUniform t.left x * typeForward t x y =
      typeUniform t.right y * typeReverse t y x) ∧
    (∀ x, x ∈ typeWords t.left →
      0 < ∑ z ∈ typeWords t.left, wordMass p z →
      typeUniform t.left x = wordMass p x / (∑ z ∈ typeWords t.left, wordMass p z)) ∧
    (∀ y, y ∈ typeWords t.right →
      0 < ∑ z ∈ typeWords t.right, wordMass (sourceOutputMarginal p w) z →
      typeUniform t.right y = wordMass (sourceOutputMarginal p w) y /
        (∑ z ∈ typeWords t.right, wordMass (sourceOutputMarginal p w) z)) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      typeForward t x y = ((typeWords t.left).card : ℝ) / (typeWords t).card ∧
      typeReverse t y x = ((typeWords t.right).card : ℝ) / (typeWords t).card) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      0 < ∑ z ∈ forwardFiber t x, wordChannel w x z →
      typeForward t x y = wordChannel w x y /
        (∑ z ∈ forwardFiber t x, wordChannel w x z)) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      0 < ∑ z ∈ reverseFiber t y, wordChannel (sourceBayesReverse p w) y z →
      typeReverse t y x = wordChannel (sourceBayesReverse p w) y x /
        (∑ z ∈ reverseFiber t y, wordChannel (sourceBayesReverse p w) y z)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
