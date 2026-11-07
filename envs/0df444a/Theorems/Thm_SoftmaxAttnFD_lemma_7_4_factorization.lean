-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_7_4_factorization
-- name    : SoftmaxAttnFD.lemma_7_4_factorization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:37.489638+00:00
-- url     : https://prove2.me/theorems/7a744121-e025-467b-935f-8e2a77c746b1
-- title:
--   Proof of Lemma 7.4, p.28 — column-anchor and row-anchor factorizations
-- statement:
--   Let $I,J$ be finite and nonempty, $x_{ij}=u_i\cdot p_j+b_i+c_j\le0$ on $I\times J$.
--
--   **Column anchor.** If $j_0\in J$ has $-L_{\rm anc}\le x_{ij_0}$ for all $i\in I$, put $p'_j=p_j-p_{j_0}$, $c'_j=c_j-c_{j_0}$, $M'_j=\max_{i\in I}p'_j\cdot u_i$, $T_{ji}=e^{p'_j\cdot u_i-M'_j}$, $d^{\rm row}_i=e^{L_{\rm anc}+x_{ij_0}}$ and $d^{\rm col}_j=e^{c'_j+M'_j-L_{\rm anc}}$. Then $x_{ij}-x_{ij_0}=u_i\cdot p'_j+c'_j$, $S_{ij}=d^{\rm row}_iT_{ji}d^{\rm col}_j$, $S_{IJ}w_J=d^{\rm row}\odot T^\top(d^{\rm col}\odot w_J)$, $1\le d^{\rm row}_i\le e^{L_{\rm anc}}$ and $0<d^{\rm col}_j\le1$.
--
--   **Row anchor.** If $i_0\in I$ has $-L_{\rm anc}\le x_{i_0j}$ for all $j\in J$, put $u'_i=u_i-u_{i_0}$, $M'_i=\max_{j\in J}u'_i\cdot p_j$, $T_{ij}=e^{u'_i\cdot p_j-M'_i}$, $d^{\rm row}_i=e^{b_i-b_{i_0}+M'_i}$ and $d^{\rm col}_j=e^{x_{i_0j}}$. Then $S_{IJ}w_J=d^{\rm row}\odot T(d^{\rm col}\odot w_J)$, $0<d^{\rm row}_i\le e^{L_{\rm anc}}$ and $e^{-L_{\rm anc}}\le d^{\rm col}_j\le1$.
--
--   This reduces an anchor block of a biased product in dimension $d-1$ to one shifted-kernel product in dimension $d-1$.
--
--   Differences from the source:
--   - generalization: rational data of a BP_{d−1} instance, restricted to a block → real data on any finite nonempty index sets; any dimension e; reason: the identities and bounds hold for reals; the page's block is an instance
--   - encoding: Lemma 7.4 as printed also has an expected-time clause → this item is the factorization inside its proof, titled as such, and the time clause is not stated here; reason: the time clause needs a procedure encoding and is carried by Proposition 5.6 and the goal
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Proof of Lemma 7.4, p.28

import Mathlib

namespace SoftmaxAttnFD

/-- **Proof of Lemma 7.4, p.28** (arXiv:2611.06055, sha256 a60f7609…): the column-anchor and row-anchor
factorizations of a block, with the bounds on their diagonal factors.

**Formalization Note** This item is the mathematics inside the proof, and not Lemma 7.4 itself: the
lemma's expected-time clause and its algorithm are carried by Proposition 5.6. The data are real. The
hypotheses are the block (`I`, `J` nonempty), nonpositive scores on the block, and the anchor
condition. -/
theorem lemma_7_4_factorization {ι κ : Type*} (e : ℕ) (I : Finset ι) (J : Finset κ)
    (hI : I.Nonempty) (hJ : J.Nonempty) (u : ι → Fin e → ℝ) (p : κ → Fin e → ℝ)
    (bi : ι → ℝ) (c : κ → ℝ) (x : ι → κ → ℝ) (hx : ∀ i j, x i j = u i ⬝ᵥ p j + bi i + c j)
    (hneg : ∀ i ∈ I, ∀ j ∈ J, x i j ≤ 0) (Lanc : ℝ) (w : κ → ℝ) :
    (∀ j₀ ∈ J, (∀ i ∈ I, -Lanc ≤ x i j₀) →
      let p' : κ → Fin e → ℝ := fun j => p j - p j₀
      let c' : κ → ℝ := fun j => c j - c j₀
      let M' : κ → ℝ := fun j => I.sup' hI fun i => p' j ⬝ᵥ u i
      let T : κ → ι → ℝ := fun j i => Real.exp (p' j ⬝ᵥ u i - M' j)
      let drow : ι → ℝ := fun i => Real.exp (Lanc + x i j₀)
      let dcol : κ → ℝ := fun j => Real.exp (c' j + M' j - Lanc)
      (∀ i ∈ I, ∀ j ∈ J, x i j - x i j₀ = u i ⬝ᵥ p' j + c' j) ∧
      (∀ i ∈ I, ∀ j ∈ J, Real.exp (x i j) = drow i * T j i * dcol j) ∧
      (∀ i ∈ I, ∑ j ∈ J, Real.exp (x i j) * w j = drow i * ∑ j ∈ J, T j i * (dcol j * w j)) ∧
      (∀ i ∈ I, 1 ≤ drow i ∧ drow i ≤ Real.exp Lanc) ∧
      (∀ j ∈ J, 0 < dcol j ∧ dcol j ≤ 1)) ∧
    (∀ i₀ ∈ I, (∀ j ∈ J, -Lanc ≤ x i₀ j) →
      let u' : ι → Fin e → ℝ := fun i => u i - u i₀
      let M' : ι → ℝ := fun i => J.sup' hJ fun j => u' i ⬝ᵥ p j
      let T : ι → κ → ℝ := fun i j => Real.exp (u' i ⬝ᵥ p j - M' i)
      let drow : ι → ℝ := fun i => Real.exp (bi i - bi i₀ + M' i)
      let dcol : κ → ℝ := fun j => Real.exp (x i₀ j)
      (∀ i ∈ I, ∀ j ∈ J, Real.exp (x i j) = drow i * T i j * dcol j) ∧
      (∀ i ∈ I, ∑ j ∈ J, Real.exp (x i j) * w j = drow i * ∑ j ∈ J, T i j * (dcol j * w j)) ∧
      (∀ i ∈ I, 0 < drow i ∧ drow i ≤ Real.exp Lanc) ∧
      (∀ j ∈ J, Real.exp (-Lanc) ≤ dcol j ∧ dcol j ≤ 1)) := by sorry

end SoftmaxAttnFD
