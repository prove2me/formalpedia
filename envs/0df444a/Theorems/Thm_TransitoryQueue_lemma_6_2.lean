-- Prove2me | Theorems.Thm_TransitoryQueue_lemma_6_2
-- name    : TransitoryQueue.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:25.186137+00:00
-- url     : https://prove2.me/theorems/575538cc-ed66-42c6-bce6-8fa93f22ad0e
-- title:
--   Lemma 6.2 — the running infimum is 1-Lipschitz in the sup norm
-- statement:
--   Let $f,g$ be real functions on $[0,\infty)$ with $|f(t)-g(t)|\le\delta$ for all $t\ge0$, and let $f$ be bounded below on every interval $[0,t]$. Then for every $t\ge0$,
--
--   $$\Bigl|\inf_{0\le u\le t}f(u)-\inf_{0\le u\le t}g(u)\Bigr|\le\delta,\qquad\text{hence}\qquad|\phi(f)(t)-\phi(g)(t)|\le2\delta.$$
--
--   The second bound is how the lemma is used ((110), p.35): it transfers a strong embedding of a process to its reflection.
--
--   Differences from the source:
--   - generalization: sup_{t∈[0,∞)} |f(t) − g(t)| < δ (102) → |f(t) − g(t)| ≤ δ for every t ≥ 0; reason: a weaker hypothesis; it covers (102)
--   - generalization: conclusion (103) on the running infima → (103) and the bound |φ(f)(t) − φ(g)(t)| ≤ 2δ; reason: the added bound is the consequence the paper draws in (110)
--   - encoding: f, g real-valued on [0, ∞) (infima may be −∞, then both are) → f bounded below on each [0, t]; reason: a real infimum of a set unbounded below is 0 in Lean; when f is bounded below so is g, and when it is not both infima are −∞ on the page
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Lemma 6.2, eqs. (102)–(103), p.34; its use in (110), p.35

import Mathlib
import Definitions.Def_TransitoryQueue_reflect

namespace TransitoryQueue

/-- **Lemma 6.2 (the running infimum is 1-Lipschitz in the sup norm).** Let `f, g` be real
functions on `[0, ∞)` with `|f(t) - g(t)| ≤ δ` for all `t ≥ 0`, and let `f` be bounded below on
every `[0, t]`. Then for all `t ≥ 0`,
`|inf_{0≤u≤t} f(u) - inf_{0≤u≤t} g(u)| ≤ δ`, and hence `|φ(f)(t) - φ(g)(t)| ≤ 2δ`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Lemma 6.2, p.34, eqs. (102)–(103), and its use in (110), p.35.

**Formalization Note** The page assumes `sup_t |f(t) - g(t)| < δ`; the Lean hypothesis
`|f(t) - g(t)| ≤ δ` for every `t` is weaker. On the page an infimum may be `-∞` (then both are);
in Lean a real infimum of a set unbounded below is `0`, so `f` is assumed bounded below on each
`[0, t]` (then so is `g`). The reflection bound is the consequence the paper uses in (110). -/
theorem lemma_6_2 (f g : ℝ → ℝ) (δ : ℝ) (hfg : ∀ t : ℝ, 0 ≤ t → |f t - g t| ≤ δ)
    (hf : ∀ t : ℝ, 0 ≤ t → BddBelow (f '' Set.Icc 0 t)) (t : ℝ) (ht : 0 ≤ t) :
    |(⨅ u : Set.Icc (0 : ℝ) t, f u) - ⨅ u : Set.Icc (0 : ℝ) t, g u| ≤ δ ∧
      |reflect f t - reflect g t| ≤ 2 * δ := by sorry

end TransitoryQueue
