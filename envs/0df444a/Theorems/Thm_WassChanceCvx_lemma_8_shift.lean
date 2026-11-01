-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_8_shift
-- name    : WassChanceCvx.lemma_8_shift
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:12.674197+00:00
-- url     : https://prove2.me/theorems/ed2bddc5-bcf5-4deb-8353-4eb344ac2acb
-- title:
--   Lemma 8 (corrected: $\alpha\le1$ or $\alpha=+\infty$) — $f-c$ is α-concave on $\{f>c\}$
-- statement:
--   Let $f:\mathbb R^n\to[0,\infty)$ be α-concave on $\mathbb R^n$, where $\alpha\in[-\infty,1]$ or $\alpha=+\infty$, and let $c\ge0$. Then $D=\{x\in\mathbb R^n: f(x)>c\}$ is convex and
--
--   $$
--   g(x):=f(x)-c\quad\text{is α-concave on } D.
--   $$
--
--   Theorem 1's proof applies it to $(x,t)\mapsto\mathbb P[f(x,\zeta)\ge t]$ with $c=1-\epsilon$, to obtain the α-concavity of $\psi$.
--
--   Differences from the source:
--   - correction: $\alpha\in\overline{\mathbb R}$ → $\alpha\le1$ or $\alpha=+\infty$; reason: the printed lemma is false for $\alpha\in(1,\infty)$: $f(x)=\sqrt{\max\{x,0\}}$ on $\mathbb R$ is 2-concave, $c=1$, and $g(10)=2.162\ldots<2.236\ldots=m_2(g(4),g(16);\tfrac12)$; the proof's $\alpha\ge1$ branch applies Proposition 6 to $-c$, which is not nonnegative
--   - reading: $g$ is α-concave on $D$ → also concludes that $D$ is convex; reason: Definition 1 defines α-concavity only on convex sets; the proof notes that $D$ is convex
--   - encoding: $f:\mathbb R^n\to\mathbb R_+$ α-concave → `IsAlphaConcaveOn α univ f`, which includes $f\ge0$; reason: same condition
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: $\mathbb R^n$ → `Fin n → ℝ`; reason: the same space
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 8, p.35

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveOn

namespace WassChanceCvx

/-- **Lemma 8 (subtracting a constant preserves α-concavity), corrected.**
Shen, Jiang, arXiv:2111.02486v2, Lemma 8, p.35: "If the function `f : ℝⁿ → ℝ₊` is an α-concave
function with `α ∈ ℝ̄` and `c ∈ ℝ₊` is a constant, then `g(x) := f(x) − c` is α-concave on
`D := {x ∈ ℝⁿ : f(x) > c}`."

**Correction.** The range of `α` is restricted to `α ≤ 1` or `α = +∞`. For `α ∈ (1, +∞)` the
lemma is false: `f(x) = √(max{x, 0})` on `ℝ` is 2-concave, `c = 1`, and
`g(10) = 2.162… < 2.236… = m₂(g(4), g(16); ½)`. (The proof's `α ≥ 1` branch appeals to
Proposition 6 with the function `−c`, which is not nonnegative.)

**Formalization Note.** "α-concave on `ℝⁿ`" is `IsAlphaConcaveOn α univ f`, which includes
`f ≥ 0`. The conclusion also states that `D` is convex (noted in the paper's proof), since
Definition 1 defines α-concavity on convex sets only. -/
theorem lemma_8_shift {n : ℕ} (f : (Fin n → ℝ) → ℝ) (α : EReal) (hα : α ≤ 1 ∨ α = ⊤)
    (hf : IsAlphaConcaveOn α Set.univ f) (c : ℝ) (hc : 0 ≤ c) :
    Convex ℝ {x | c < f x} ∧ IsAlphaConcaveOn α {x | c < f x} (fun x => f x - c) := by sorry

end WassChanceCvx
