-- Prove2me | Theorems.Thm_PerturbedWF_lemma_2_4
-- name    : PerturbedWF.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:46:57.050714+00:00
-- url     : https://prove2.me/theorems/9a818a4f-339c-4eb9-bd65-bdbde5d152c9
-- title:
--   Lemma 2.4: $H(q)=W^*(Aq)$ is Lipschitz, and for a.e. $q$ the maximizer $X$ is unique with $\nabla H(q)=A^{\mathsf T}X$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$ and $W\in\mathcal W(\mathcal C)$. For some $m\in\mathbb N$ let $A\in\mathbb R^{n\times m}$ be a matrix with pairwise distinct rows, and define $H:\mathbb R^m\to\mathbb R$ by $H(q)=W^*(Aq)$. Then $H$ is Lipschitz continuous and, for almost every $q\in\mathbb R^m$ (Lebesgue measure):
--   1. there is a unique $X\in\arg\max_{x\in\mathcal C}\{\langle Aq,x\rangle-W(x)\}$;
--   2. $\nabla H(q)=A^{\mathsf T}X$.
--
--   This makes the randomized algorithm well defined almost surely and identifies its position with the gradient of the potential.
--
--   **Formalization Note.** Rows are $A_i\in\mathbb R^m$ (`A : ι → Fin m → ℝ`), distinct rows means $A$ injective, $H(q)$ is the real value of the `EReal` conjugate. Part 2 is `HasFDerivAt H ℓ q` for the linear map $\ell(p)=\sum_k(\sum_iA_{ik}X_i)p_k$, with $X$ the unique maximizer of part 1.
--
--   Differences from the source:
--   - encoding: ∇H(q) = AᵀX → HasFDerivAt H (p ↦ Σ_k (Aᵀ X)_k p_k) q; reason: a gradient at q is a Fréchet derivative there; same content
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 2.4, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF

open MeasureTheory

/-- **Lemma 2.4** (p.7, PDF p.8). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Let `W ∈ W(C)`, `m ∈ ℕ`, and let `A ∈ ℝ^{n×m}` have pairwise distinct rows. Let
`H : ℝ^m → ℝ`, `H(q) = W*(Aq)`. Then `H` is Lipschitz continuous and, for almost every
`q ∈ ℝ^m`:
1. there is a unique `X ∈ argmax_{x ∈ C} {⟨Aq, x⟩ − W(x)}`;
2. `∇H(q) = Aᵀ X`.

**Formalization Note.** `A : ι → Fin m → ℝ` (row `i` is `A i`), pairwise distinct rows is
injectivity, `Aq = matVec A q`. `H(q)` is the real value of the `EReal` conjugate (finite for
`W ∈ W(C)`). "Almost every" is for Lebesgue measure on all of `ℝ^m`. The `X` of part 2 is the
unique maximizer of part 1, and `∇H(q) = AᵀX` is `HasFDerivAt` with the linear map
`p ↦ ∑_k (∑_i A i k · X_i) p_k`. -/
theorem lemma_2_4 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (W : (ι → ℝ) → EReal)
    (hW : WClass C d W) (m : ℕ) (A : ι → Fin m → ℝ) (hA : Function.Injective A) :
    (∃ K, LipschitzWith K (fun q : Fin m → ℝ => (conj C W (matVec A q)).toReal)) ∧
      ∀ᵐ q ∂(volume : Measure (Fin m → ℝ)), ∃ X ∈ C,
        (∀ y ∈ C, ((dot (matVec A q) y : ℝ) : EReal) - W y ≤
          ((dot (matVec A q) X : ℝ) : EReal) - W X) ∧
        (∀ Y ∈ C, (∀ y ∈ C, ((dot (matVec A q) y : ℝ) : EReal) - W y ≤
          ((dot (matVec A q) Y : ℝ) : EReal) - W Y) → Y = X) ∧
        HasFDerivAt (fun p : Fin m → ℝ => (conj C W (matVec A p)).toReal)
          (∑ k, (∑ i, A i k * X i) • ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin m => ℝ) k) q := by sorry

end PerturbedWF
