-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_marginalValue_antitone_capacity
-- name    : RevenueOrdered.Nesting.marginalValue_antitone_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:27.697373+00:00
-- url     : https://prove2.me/theorems/0653f2d5-ac76-4dde-97ab-77c01e1b0064
-- title:
--   Talluri–van Ryzin Lemma 4, as cited on p. 36 — ∆𝒥_t(q) is non-increasing in q
-- statement:
--   Consider the revenue-ordered multi-period dynamic program of §5, with choice probabilities $\mathcal P$ satisfying axioms (i)–(iii) and positive revenues $r$. For every $t\ge 0$ periods remaining and every $q\ge 1$,
--   $$
--   \Delta\mathcal J_t(q+1)\le\Delta\mathcal J_t(q),
--   $$
--   that is, the marginal value of capacity is non-increasing in the number of units left.
--
--   The paper does not prove this: it cites Talluri and van Ryzin (2004), Lemma 4, and states that the inequality "always holds, regardless of the discrete choice model under consideration (that is, the three axioms (i), (ii) and (iii) are enough for this property to hold)". Talluri and van Ryzin prove it for the dynamic program that optimises over all offer sets; here it is stated for the dynamic program restricted to revenue-ordered assortments, which is the one the paper applies it to. Combined with Lemma .1 it gives the capacity half of Theorem 5.1.
--
--   **Formalization Note** The paper's form is $\Delta\mathcal J_{t-1}(q-1)\ge\Delta\mathcal J_{t-1}(q)$ for $q\ge 2$; it is written here with $q+1$ and $q$ ($q\ge 1$) and any $t\ge 0$. Only axioms (i)–(iii) (`IsChoiceSystem`) are assumed, as the paper says suffices.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 36, Appendix B, proof of Theorem 5.1, citing Talluri and Van Ryzin [44, Lemma 4]

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- App. B, p. 36, citing Talluri–van Ryzin (2004), Lemma 4: the marginal value of capacity is
non-increasing in the capacity, `∆𝒥_t(q + 1) ≤ ∆𝒥_t(q)` for every `t ≥ 0` and `q ≥ 1`.
Stated, as the paper says suffices, under axioms (i)–(iii) only. -/
theorem marginalValue_antitone_capacity {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsChoiceSystem P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    marginalValue P r t (q + 1) ≤ marginalValue P r t q := by sorry

end RevenueOrdered.Nesting
