-- Prove2me | Theorems.Thm_PerturbedWF_lemma_4_1
-- name    : PerturbedWF.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:43:15.624195+00:00
-- url     : https://prove2.me/theorems/7e91569f-2478-4107-af1b-188efd5e3174
-- title:
--   Lemma 4.1: on $\mathrm{supp}(W_t)$, $W_t=W_{t-1}+F_t$, and $W_t^*(v)=\max_{x\in\mathcal C}\{\langle v,x\rangle-W_{t-1}(x)-F_t(x)\}$
-- statement:
--   Consider metric allocation on the simplex $\mathcal C$ over a finite metric $d$, with initial configuration $x_0$ and requests $F_t(x)=f_t(x_{r_t})$ ($f_t:[0,1]\to\mathbb R_{\ge0}$ convex, continuous, monotone), and let $W_t$ be the work functions (4.1). For every $t\ge1$:
--   1. every $x\in\mathrm{supp}(W_t)$ satisfies $W_t(x)=W_{t-1}(x)+F_t(x)$;
--   2. for every $v\in B^*$,
--   $$W_t^*(v)=\max_{x\in\mathcal C}\{\langle v,x\rangle-W_{t-1}(x)-F_t(x)\}.$$
--
--   This is the step that converts a move of the algorithm into a decrease of the conjugate.
--
--   **Formalization Note.** $W_t$ enters `supp` and `conj` through its coercion to `EReal`. "max" is stated as: there is a maximizer $x$ of $\langle v,\cdot\rangle-W_{t-1}-F_t$ over the simplex, and $W_t^*(v)$ equals the value at $x$. The time $t$ ranges over $1\le t\le N$ for requests valid up to $N$.
--
--   Differences from the source:
--   - encoding: W_t^*(v) = max_{x∈C}{⟨v, x⟩ − W_{t−1}(x) − F_t(x)} → ∃ x in the simplex maximizing ⟨v, ·⟩ − W_{t−1} − F_t, and conj W_t v equals the value at x; reason: 'max' asserts that the maximum is attained; same content
--   - encoding: v ∈ B* = {v : ‖v‖* ≤ 1} → v ∈ dualBall d, i.e. |v_i − v_j| ≤ d(i, j) for all i, j; reason: the characterization of B* stated after (2.2), p.5 (v ∈ B* iff |v_i − v_j| ≤ d(i, j)); the same set
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 4.1, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PerturbedWF_MetricAllocation

namespace PerturbedWF

/-- **Lemma 4.1** (p.12, PDF p.13). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

For metric allocation with requests `F_t(x) = f_t(x_{r_t})` and `1 ≤ t ≤ N`:
1. every `x ∈ supp(W_t)` satisfies `W_t(x) = W_{t−1}(x) + F_t(x)`;
2. for every `v ∈ B*`, `W_t^*(v) = max_{x ∈ C} {⟨v, x⟩ − W_{t−1}(x) − F_t(x)}`.

**Formalization Note.** `W_t` enters `supp` and `conj` through its coercion to `EReal`. "max"
is stated as: there is a maximizer `x` of `⟨v, ·⟩ − W_{t−1} − F_t` over the simplex, and the
conjugate equals the value at `x`. -/
theorem lemma_4_1 {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (hd : IsFinMetric d)
    (x₀ : ι → ℝ) (hx₀ : x₀ ∈ simplex ι) (N : ℕ) (r : ℕ → ι) (f : ℕ → ℝ → ℝ)
    (hf : ∀ t ∈ Finset.Icc 1 N, IsMAReq (f t)) (t : ℕ) (ht : t ∈ Finset.Icc 1 N) :
    (∀ x ∈ supp (simplex ι) d (fun y => ((workFn d x₀ (maCost r f) t y : ℝ) : EReal)),
        workFn d x₀ (maCost r f) t x = workFn d x₀ (maCost r f) (t - 1) x + f t (x (r t))) ∧
      ∀ v ∈ dualBall d, ∃ x ∈ simplex ι,
        (∀ y ∈ simplex ι, dot v y - workFn d x₀ (maCost r f) (t - 1) y - f t (y (r t)) ≤
          dot v x - workFn d x₀ (maCost r f) (t - 1) x - f t (x (r t))) ∧
        conj (simplex ι) (fun y => ((workFn d x₀ (maCost r f) t y : ℝ) : EReal)) v =
          ((dot v x - workFn d x₀ (maCost r f) (t - 1) x - f t (x (r t)) : ℝ) : EReal) := by sorry

end PerturbedWF
