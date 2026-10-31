-- Prove2me | Theorems.Thm_SDEConvexOpt_lemma_A_4
-- name    : SDEConvexOpt.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:11.346783+00:00
-- url     : https://prove2.me/theorems/1250092c-49be-4dc9-a4ef-d7b0737086bd
-- title:
--   Lemma A.4 — if $\liminf f\neq\limsup f$, some $\alpha$ in between is exceeded along $\beta$-separated times
-- statement:
--   Let $f:\mathbb R_+\to\mathbb R$ with $\liminf_{t\to\infty}f(t)\neq\limsup_{t\to\infty}f(t)$. Then there is a real constant $\alpha$ with
--   $$
--   \liminf_{t\to\infty}f(t)<\alpha<\limsup_{t\to\infty}f(t)
--   $$
--   such that for every $\beta>0$ there is a sequence $(t_k)_{k\in\mathbb N}$ with
--   $$
--   f(t_k)>\alpha,\qquad t_{k+1}>t_k+\beta,\qquad\forall k\in\mathbb N .
--   $$
--   The lemma provides the separated times in the contradiction argument for $\lim\|\nabla f(X(t))\|=0$.
--
--   Differences from the source:
--   - encoding: $\liminf$, $\limsup$ of a real function → computed in `EReal`; reason: they may be $\pm\infty$ for an unbounded $f$; a real-valued `liminf` would give junk values
--   - encoding: $(t_k)_{k\in\mathbb N}\subset\mathbb R$ → $t_k\in\mathbb R_{\ge0}$; reason: $f$ is only defined on $\mathbb R_+$, so $f(t_k)$ requires $t_k\ge0$
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Lemma A.4, p.32

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

/-- Lemma A.4 of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.32: let `f : ℝ₊ → ℝ` with
`lim inf_{t→∞} f(t) ≠ lim sup_{t→∞} f(t)`. Then there exists a constant `α`, satisfying
`lim inf_{t→∞} f(t) < α < lim sup_{t→∞} f(t)`, such that for every `β > 0` there is a sequence
`(t_k)_{k∈ℕ}` with `f(t_k) > α` and `t_{k+1} > t_k + β` for all `k ∈ ℕ`.

**Formalization Note** `ℝ₊` is `ℝ≥0`. The `lim inf` and `lim sup` are taken in `EReal` (they may
be `±∞` for unbounded `f`), and `α` is real. The sequence takes values in `ℝ≥0`, the domain of
`f`. -/
theorem lemma_A_4 (f : ℝ≥0 → ℝ)
    (hf : liminf (fun t => (f t : EReal)) atTop ≠ limsup (fun t => (f t : EReal)) atTop) :
    ∃ α : ℝ, liminf (fun t => (f t : EReal)) atTop < (α : EReal) ∧
      (α : EReal) < limsup (fun t => (f t : EReal)) atTop ∧
      ∀ β : ℝ, 0 < β → ∃ tk : ℕ → ℝ≥0, ∀ k : ℕ, α < f (tk k) ∧ (tk k : ℝ) + β < tk (k + 1) := by sorry

end SDEConvexOpt
