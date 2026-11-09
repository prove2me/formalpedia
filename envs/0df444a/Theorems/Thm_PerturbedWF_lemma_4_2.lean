-- Prove2me | Theorems.Thm_PerturbedWF_lemma_4_2
-- name    : PerturbedWF.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:46:42.81274+00:00
-- url     : https://prove2.me/theorems/66a34bbb-0505-49e1-878d-4a9435bfeb70
-- title:
--   Lemma 4.2: the service cost of the algorithm is 1-competitive, $\sum_{t=1}^T\mathbb E[F_t(X_t)]\le\mathrm{OPT}$
-- statement:
--   Let $d$ be a metric on the finite set $[n]$ and let $A_1,\dots,A_n\in\mathbb R^m$ be pairwise distinct vectors with $\|A_i-A_j\|_1\le d(i,j)$ for all $i,j$. Consider metric allocation on the simplex $\mathcal C$ with initial configuration $x_0\in\mathcal C$ and requests $F_t(x)=f_t(x_{r_t})$, $t=1,\dots,T$, each $f_t:[0,1]\to\mathbb R_{\ge0}$ convex, continuous and monotone. Let $X_0=x_0,X_1,\dots,X_T$ be any run of the algorithm that samples $q$ uniformly from $[-1,1]^m$ and moves to a maximizer $X_t$ of $\langle Aq,x\rangle-W_t(x)$. Then the total expected service cost is at most the optimal offline cost:
--   $$\sum_{t=1}^T\mathbb E\big[F_t(X_t)\big]\le\mathrm{OPT}.$$
--
--   This is the service half of the competitive analysis; Theorem 4.3 bounds the movement half.
--
--   **Formalization Note.** Expectations are lower integrals of the nonnegative service costs under the uniform law on the cube, and the bound is `ENNReal.ofReal OPT`.
--
--   Differences from the source:
--   - generalization: the algorithm on a τ-HST with the vectors A_i of Theorem 3.4 → any finite metric d and any pairwise distinct A_i ∈ ℝ^m with ‖A_i − A_j‖₁ ≤ d(i, j); reason: Theorem 3.4's vectors have both properties (distinctness from its property 2, since d(i, j) > 0 for i ≠ j), so the statement specializes to the paper's
--   - generalization: X_t ∈ argmax over supp(W_t) (§4.1) → X_t any maximizer of ⟨Aq, ·⟩ − W_t over the whole simplex (IsAlgRun); reason: by Lemma 2.3 every maximizer over supp(W_t) is a maximizer over C, so every run of §4.1 is covered
--   - encoding: expectation E[·] over q uniform on [−1, 1]^m → lower Lebesgue integral ∫⁻ ENNReal.ofReal(·) under cubeLaw m; reason: the costs are nonnegative, so the lower integral is the expectation; no integrability or measurability of the run is needed
--   - encoding: requests F_t(x) = f_t(x_{r_t}) with f_t convex, monotone and continuous (after the [BC22] reduction, footnote 1) → sequences r, f with IsMAReq (f t) for 1 ≤ t ≤ N: convex, continuous, monotone in either direction, nonnegative on [0, 1]; reason: this is the request class the paper analyzes (p.12, 'We thus design and analyze our algorithm for this version')
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 4.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF

open MeasureTheory

/-- **Lemma 4.2** (p.12, PDF p.13). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

The total service cost of the algorithm of §4.1 is 1-competitive:
`∑_{t=1}^N E[F_t(X_t)] ≤ OPT`, where `F_t(x) = f_t(x_{r_t})`.

**Formalization Note.** Stated on any finite metric `d` and any vectors `A_i ∈ ℝ^m` that are
pairwise distinct with `‖A_i − A_j‖₁ ≤ d(i, j)` (the two properties of the vectors of Theorem 3.4
that the algorithm uses; on a `τ`-HST, Theorem 3.4's vectors have them). Every run: `X_t` any
maximizer over the simplex. Expectations are lower integrals of `ENNReal.ofReal` of the
nonnegative service cost under the uniform law on `[−1, 1]^m`. -/
theorem lemma_4_2 {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (hd : IsFinMetric d)
    (m : ℕ) (A : ι → Fin m → ℝ) (hA : Function.Injective A)
    (hA1 : ∀ i j, ∑ k, |A i k - A j k| ≤ d i j)
    (x₀ : ι → ℝ) (hx₀ : x₀ ∈ simplex ι) (N : ℕ) (r : ℕ → ι) (f : ℕ → ℝ → ℝ)
    (hf : ∀ t ∈ Finset.Icc 1 N, IsMAReq (f t))
    (X : ℕ → (Fin m → ℝ) → (ι → ℝ)) (hX : IsAlgRun d x₀ (maCost r f) A N X) :
    ∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal (f t (X t q (r t))) ∂(cubeLaw m) ≤
      ENNReal.ofReal (OPT d x₀ (maCost r f) N) := by sorry

end PerturbedWF
