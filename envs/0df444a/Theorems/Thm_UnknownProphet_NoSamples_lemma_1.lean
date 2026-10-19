-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_lemma_1
-- name    : UnknownProphet.NoSamples.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:49.748237+00:00
-- url     : https://prove2.me/theorems/a57d032e-feeb-4dbc-8fba-1b8a3530e946
-- title:
--   Lemma 1, p. 6 — value-oblivious rule on an infinite set
-- statement:
--   For every $\varepsilon>0$, every sample count $k\ge0$, horizon $n$, and ratio $\alpha$, if some $(k,n)$ stopping rule achieves guarantee $\alpha$, then one such rule is $\varepsilon$ value oblivious on an infinite set $V$:
--
--   $$
--   \exists r,\ \operatorname{Guarantee}(r,\alpha)\ \land\ \exists V\subseteq\mathbb N,\ |V|=\infty\ \land\ r\text{ is }\varepsilon\text{ value oblivious on }V.
--   $$
--
--   This structural result supplies the approximately record-based rule used for the hard distribution.
--
--   **Formalization Note** The guarantee ranges over finitely supported nonnegative laws. The paper takes $n$ positive; at $n=0$ both the premise and conclusion hold trivially. Lean's natural numbers permit $0$ in $V$.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 6, Lemma 1

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Lemma 1, p. 6: an arbitrary guarantee can be achieved by a rule
that is approximately value-oblivious on an infinite set. -/
theorem lemma_1 (ε : ℝ) (hε : 0 < ε) (k n : ℕ) (α : ℝ)
    (h : ∃ R : StoppingRule k n, HasGuarantee R α) :
    ∃ R : StoppingRule k n,
      HasGuarantee R α ∧ ∃ V : Set ℕ, V.Infinite ∧ ValueOblivious ε R V := by sorry

end UnknownProphet.NoSamples
