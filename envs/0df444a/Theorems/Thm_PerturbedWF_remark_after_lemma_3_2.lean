-- Prove2me | Theorems.Thm_PerturbedWF_remark_after_lemma_3_2
-- name    : PerturbedWF.remark_after_lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:52.311385+00:00
-- url     : https://prove2.me/theorems/15dd7cfc-9f70-468e-8428-62a066139a0c
-- title:
--   Remark after Lemma 3.2: one-directional movement for a non-decreasing request $f(x_r)$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$, $W\in\mathcal W(\mathcal C)$, let $f:[0,\infty)\to\mathbb R\cup\{\infty\}$ be **non-decreasing** and lower semicontinuous, and let $r\in[n]$. For every $v\in\mathbb R^n$ and every $X\in\arg\max_{x\in\mathcal C}\{\langle v,x\rangle-W(x)\}$ there exists $X'\in\arg\max_{x\in\mathcal C}\{\langle v,x\rangle-W(x)-f(x_r)\}$ such that
--   1. $X'-X=\sum_{i\ne r}\beta_i(e_i-e_r)$ for some $\beta\in\mathbb R^n_{\ge0}$;
--   2. if moreover $\mathcal C\subseteq\mathbb Z^n_{\ge0}$ and $f$ is constant on $[0,X_r-1]$, then $X'-X=e_i-e_r$ for some $i\in[n]$.
--
--   A request that penalizes mass at $r$ only moves mass out of $r$; Theorem 4.3 uses this case for non-decreasing requests.
--
--   **Formalization Note.** Conventions as in Lemma 3.2. "Constant on $[0,X_r-1]$" is $f(s)=f(0)$ for $0\le s\le X_r-1$ (vacuous when $X_r<1$).
--
--   Differences from the source:
--   - reading: 'the same statements hold for a non-decreasing f, where we would simply multiply one side by −1 in the equations above' → X′ − X = Σ_{i≠r} β_i(e_i − e_r) and, in the integral case, X′ − X = e_i − e_r; reason: negating one side of (3.1) and of X′ − X = e_r − e_i gives these; it is the form used in the proof of Theorem 4.3 (X_t − X_{t−1} = Σ β_i(e_i − e_r))
--   - reading: 'Moreover … then X′ − X = e_r − e_i' after 'there exists X′' → one X′ satisfies both conclusions; reason: as in Lemma 3.2
--   - encoding: f : [0, ∞) → ℝ ∪ {∞}; argmax of ⟨v, x⟩ − W(x) − f(x_r) over C; C ⊆ ℤⁿ≥0 → f : ℝ → EReal, ≠ ⊥ on [0, ∞), with monotonicity and lower semicontinuity on [0, ∞); the objective computed in EReal (−∞ where W or f is ∞); IsIntegral C; reason: Lean convention; values of f off [0, ∞) are never used (coordinates of C are nonnegative); the same instances
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Remark after Lemma 3.2, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

/-- **Remark after Lemma 3.2** (p.9, PDF p.10): Lemma 3.2 for a non-decreasing `f`. C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

"The same statements hold for a non-decreasing function `f`, where we would simply multiply one
side by −1 in the equations above. For the integral setting, the assumption on `f` becomes that
`f` is constant on `[0, X_r − 1]`." Explicitly: let `W ∈ W(C)`, `f : [0, ∞) → ℝ ∪ {∞}`
non-decreasing and lower semicontinuous, `r ∈ [n]`, `v ∈ ℝⁿ` and
`X ∈ argmax_{x ∈ C} {⟨v, x⟩ − W(x)}`. Then some `X' ∈ argmax_{x ∈ C} {⟨v, x⟩ − W(x) − f(x_r)}`
satisfies `X' − X = ∑_{i ≠ r} β_i (e_i − e_r)` for some `β ∈ ℝⁿ_{≥0}`, and, if `C ⊆ ℤⁿ_{≥0}` and `f`
is constant on `[0, X_r − 1]`, `X' − X = e_i − e_r` for some `i ∈ [n]`.

**Formalization Note.** "Multiply one side by −1" is read as the sign flip of the displacement
(mass now leaves `r`). Conventions as in `lemma_3_2`. -/
theorem remark_after_lemma_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (W : (ι → ℝ) → EReal)
    (hW : WClass C d W) (f : ℝ → EReal) (hf_ne : ∀ s, 0 ≤ s → f s ≠ ⊥)
    (hf_mono : MonotoneOn f (Set.Ici 0)) (hf_lsc : LowerSemicontinuousOn f (Set.Ici 0))
    (r : ι) (v : ι → ℝ) (X : ι → ℝ) (hX : X ∈ C)
    (hXmax : ∀ y ∈ C, ((dot v y : ℝ) : EReal) - W y ≤ ((dot v X : ℝ) : EReal) - W X) :
    ∃ X' ∈ C,
      (∀ y ∈ C, ((dot v y : ℝ) : EReal) - W y - f (y r) ≤
        ((dot v X' : ℝ) : EReal) - W X' - f (X' r)) ∧
      (∃ β : ι → ℝ, (∀ i, 0 ≤ β i) ∧
        X' - X = ∑ i ∈ Finset.univ.erase r, β i • (Pi.single i (1 : ℝ) - Pi.single r (1 : ℝ))) ∧
      (IsIntegral C → (∀ s, 0 ≤ s → s ≤ X r - 1 → f s = f 0) →
        ∃ i, X' - X = Pi.single i (1 : ℝ) - Pi.single r (1 : ℝ)) := by sorry

end PerturbedWF
