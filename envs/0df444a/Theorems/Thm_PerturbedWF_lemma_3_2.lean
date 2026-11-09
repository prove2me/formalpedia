-- Prove2me | Theorems.Thm_PerturbedWF_lemma_3_2
-- name    : PerturbedWF.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:42:07.102177+00:00
-- url     : https://prove2.me/theorems/f2910efd-5c46-40cd-a738-16859cf7d2bb
-- title:
--   Lemma 3.2: one-directional movement for a non-increasing request $f(x_r)$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$, $W\in\mathcal W(\mathcal C)$, let $f:[0,\infty)\to\mathbb R\cup\{\infty\}$ be non-increasing and lower semicontinuous, and let $r\in[n]$. For every $v\in\mathbb R^n$ and every $X\in\arg\max_{x\in\mathcal C}\{\langle v,x\rangle-W(x)\}$ there exists
--   $$X'\in\arg\max_{x\in\mathcal C}\{\langle v,x\rangle-W(x)-f(x_r)\}$$
--   such that
--   1. $X'-X=\sum_{i\ne r}\beta_i(e_r-e_i)$ for some $\beta\in\mathbb R^n_{\ge0}$ (3.1);
--   2. if moreover $\mathcal C\subseteq\mathbb Z^n_{\ge0}$ and $f$ is constant on $[X_r+1,\infty)$, then $X'-X=e_r-e_i$ for some $i\in[n]$.
--
--   A request that rewards mass at $r$ only moves mass into $r$; this one-sink property drives the movement bound.
--
--   **Formalization Note.** $f$ is a function $\mathbb R\to$ `EReal`, used on $[0,\infty)$, with values $\ne-\infty$ there; the objective is computed in `EReal` and equals $-\infty$ where $W$ or $f$ is infinite. One $X'$ satisfies both conclusions; in 2, $i=r$ (i.e. $X'=X$) is allowed.
--
--   Differences from the source:
--   - reading: 'Moreover, if C ⊆ ℤⁿ≥0 … then X′ − X = e_r − e_i' after 'there exists X′ … such that (3.1)' → one X′ satisfies both (3.1) and the integral clause; reason: the 'Moreover' continues the statement about the same X′, as in the proof (the closest maximizer)
--   - encoding: f : [0, ∞) → ℝ ∪ {∞}; argmax of ⟨v, x⟩ − W(x) − f(x_r) over C; C ⊆ ℤⁿ≥0 → f : ℝ → EReal, ≠ ⊥ on [0, ∞), with monotonicity and lower semicontinuity on [0, ∞); the objective computed in EReal (−∞ where W or f is ∞); IsIntegral C; reason: Lean convention; values of f off [0, ∞) are never used (coordinates of C are nonnegative); the same instances
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

/-- **Lemma 3.2** (p.8, PDF p.9). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Let `W ∈ W(C)`, let `f : [0, ∞) → ℝ ∪ {∞}` be non-increasing and lower semicontinuous, and let
`r ∈ [n]`. For any `v ∈ ℝⁿ` and `X ∈ argmax_{x ∈ C} {⟨v, x⟩ − W(x)}` there exists
`X' ∈ argmax_{x ∈ C} {⟨v, x⟩ − W(x) − f(x_r)}` such that
`X' − X = ∑_{i ≠ r} β_i (e_r − e_i)` for some `β ∈ ℝⁿ_{≥0}` (3.1). Moreover, if `C ⊆ ℤⁿ_{≥0}`
and `f` is constant on `[X_r + 1, ∞)`, then `X' − X = e_r − e_i` for some `i ∈ [n]`.

**Formalization Note.** `f : ℝ → EReal`, used on `[0, ∞)`, with values `≠ ⊥` there. The
objective is computed in `EReal` (it is `⊥` where `W` or `f` is `∞`). One `X'` satisfies both
conclusions. `i = r` is allowed in the integral clause (then `X' = X`). -/
theorem lemma_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (W : (ι → ℝ) → EReal)
    (hW : WClass C d W) (f : ℝ → EReal) (hf_ne : ∀ s, 0 ≤ s → f s ≠ ⊥)
    (hf_anti : AntitoneOn f (Set.Ici 0)) (hf_lsc : LowerSemicontinuousOn f (Set.Ici 0))
    (r : ι) (v : ι → ℝ) (X : ι → ℝ) (hX : X ∈ C)
    (hXmax : ∀ y ∈ C, ((dot v y : ℝ) : EReal) - W y ≤ ((dot v X : ℝ) : EReal) - W X) :
    ∃ X' ∈ C,
      (∀ y ∈ C, ((dot v y : ℝ) : EReal) - W y - f (y r) ≤
        ((dot v X' : ℝ) : EReal) - W X' - f (X' r)) ∧
      (∃ β : ι → ℝ, (∀ i, 0 ≤ β i) ∧
        X' - X = ∑ i ∈ Finset.univ.erase r, β i • (Pi.single r (1 : ℝ) - Pi.single i (1 : ℝ))) ∧
      (IsIntegral C → (∀ s, X r + 1 ≤ s → f s = f (X r + 1)) →
        ∃ i, X' - X = Pi.single r (1 : ℝ) - Pi.single i (1 : ℝ)) := by sorry

end PerturbedWF
