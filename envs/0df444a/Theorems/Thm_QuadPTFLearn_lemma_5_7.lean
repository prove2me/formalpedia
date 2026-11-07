-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_5_7
-- name    : QuadPTFLearn.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:50.158112+00:00
-- url     : https://prove2.me/theorems/2c05e7d0-9093-499f-9c80-b834b7df281e
-- title:
--   Lemma 5.7, p.33 — $\mathrm{Rand}_f(v)>\alpha$ implies $\mathbb E_w[\sum_{s\in S_w}\phi(s)]>\alpha/C$
-- statement:
--   Let $f:\mathbb R^d\to\{0,1\}$ be an intersection of $k$ degree-2 PTFs and $v\in S^{d-1}$. For $w\perp v$ write $f_w(s)=f(sv+w)$ and let $S_w\subseteq\mathbb R$ be the set of jump points of $f_w$. There is a constant $C>1$ such that for every $\alpha\in(0,1)$ and every unit vector $v$, if $\mathrm{Rand}_f(v)>\alpha$, then
--   $$\mathbb E_{w\sim N(0,I)}\Big[\sum_{s\in S_w}\phi(s)\Big]>\alpha/C,$$
--   where $\phi$ is the standard normal density.
--
--   Non-trivial randomized error along $v$ forces non-trivial Gaussian-weighted boundary mass along $v$.
--
--   Differences from the source:
--   - reading: There is a constant C > 1 (stated after f) → C universal, chosen before d, k, f; reason: the non-weaker reading; the proof's constant is 1/ϕ(1)
--   - encoding: S_w the set of jump points; E_{w∼N(0,I)} → points where both one-sided limits of f_w exist and differ; w = proj_{v⊥}x with x ∼ N(0, I_d); the expectation of the nonnegative sum as a lower Lebesgue integral in [0, ∞]; reason: the same quantity
--   - encoding: i ∈ [k], k ∈ ℤ₊ → k a natural number, k = 0 not excluded; reason: at k = 0 f ≡ 1, so Rand_f(v) = 0 < α and the statement is vacuous; no instance of the source changes
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 5.7, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 5.7, p.33 (PDF p.35).

Let `f : ℝᵈ → {0, 1}` be an intersection of `k` degree-2 PTFs and `v` a unit vector. For
`w ⊥ v` let `f_w(s) = f(sv + w)` and `S_w` the set of jump points of `f_w`. There is a constant
`C > 1` such that for every `α ∈ (0, 1)` and every unit `v`, if `Rand_f(v) > α` then
`E_{w∼N(0,I)}[Σ_{s∈S_w} ϕ(s)] > α/C`.

**Formalization Note.** `C` is read as universal (chosen before `d, k, f`). `w = proj_{v⊥} x` with
`x ∼ N(0, I_d)`; the expectation of the nonnegative sum is a lower Lebesgue integral in `ℝ≥0∞`. -/
theorem lemma_5_7 :
    ∃ C : ℝ, 1 < C ∧
      ∀ (d k : ℕ) (q : Fin k → Poly d), IsQuadFamily q →
      ∀ α : ℝ, 0 < α → α < 1 → ∀ v : Pt d, ‖v‖ = 1 → α < Rand (ptfInd q) v →
        ENNReal.ofReal (α / C) <
          ∫⁻ x, ∑' s : jumpSet (layer (ptfInd q) v (perp v x)), ENNReal.ofReal (phi s)
            ∂gauss d := by sorry

end QuadPTFLearn
