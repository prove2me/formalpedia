-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_marginalValue_mono_time
-- name    : RevenueOrdered.Nesting.marginalValue_mono_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:37.470419+00:00
-- url     : https://prove2.me/theorems/336e0a2d-6bab-4763-be15-d659641fb4be
-- title:
--   Talluri–van Ryzin Lemma 5, as cited on p. 37 — ∆𝒥_t(q) is non-decreasing in t
-- statement:
--   Consider the revenue-ordered multi-period dynamic program of §5, with choice probabilities $\mathcal P$ satisfying axioms (i)–(iii) and positive revenues $r$. For every $t\ge 0$ and every $q\ge 1$ units left,
--   $$
--   \Delta\mathcal J_t(q)\le\Delta\mathcal J_{t+1}(q),
--   $$
--   that is, the marginal value of capacity is non-decreasing in the number of periods remaining.
--
--   The paper does not prove this: it cites Talluri and van Ryzin (2004), Lemma 5, and states that the inequality "always holds, regardless of the discrete choice model under consideration". Talluri and van Ryzin prove it for the dynamic program that optimises over all offer sets; here it is stated for the dynamic program restricted to revenue-ordered assortments, which is the one the paper applies it to. Combined with Lemma .1 it gives the time half of Theorem 5.1.
--
--   **Formalization Note** The paper's form is $\Delta\mathcal J_{t-1}(q)\ge\Delta\mathcal J_{t-2}(q)$ for $t\ge 2$; it is written here with $t+1$ and $t$ ($t\ge 0$). Only axioms (i)–(iii) (`IsChoiceSystem`) are assumed, consistently with the companion capacity statement.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 37, Appendix B, proof of Theorem 5.1, citing Talluri and Van Ryzin [44, Lemma 5]

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- App. B, p. 37, citing Talluri–van Ryzin (2004), Lemma 5: the marginal value of capacity is
non-decreasing in the time remaining, `∆𝒥_t(q) ≤ ∆𝒥_{t+1}(q)` for every `t ≥ 0` and `q ≥ 1`.
Stated, as the paper says suffices, under axioms (i)–(iii) only. -/
theorem marginalValue_mono_time {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsChoiceSystem P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    marginalValue P r t q ≤ marginalValue P r (t + 1) q := by sorry

end RevenueOrdered.Nesting
