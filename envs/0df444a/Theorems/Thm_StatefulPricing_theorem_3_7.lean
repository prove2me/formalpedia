-- Prove2me | Theorems.Thm_StatefulPricing_theorem_3_7
-- name    : StatefulPricing.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:21.429989+00:00
-- url     : https://prove2.me/theorems/4675e867-cbe7-49c3-88f4-fa02cd8fa78d
-- title:
--   Theorem 3.7 (Kalai–Vempala; corrected: $\Delta\ge1$): OLSC regret $O(\sqrt{\Delta T\log|\Gamma|})$
-- statement:
--   There is an absolute constant $K_1$ such that for every switching cost $\Delta\ge1$, every horizon $T$ and every finite nonempty set $\Gamma$ of experts there is a randomized online OLSC algorithm whose regret with switching cost $\Delta$ satisfies
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T F_t(\gamma)-\mathbb E\Big[\sum_{t=1}^T F_t(\gamma_t)-\Delta\sum_{t=2}^T\mathbf 1_{\gamma_t\neq\gamma_{t-1}}\Big]\le K_1\sqrt{\Delta\,T\log|\Gamma|}
--   $$
--   for every reward sequence $F_1,\dots,F_T:\Gamma\to[0,1]$ fixed in advance, the random variable inside the expectation being integrable.
--
--   This is the result of Kalai and Vempala (2005) that C&S uses as a black box, with $\Delta=\sigma$.
--
--   Differences from the source:
--   - correction: switching cost $\Delta>0$ → $\Delta\ge1$; reason: false for small $\Delta$: with $T=1$ and $\Gamma=\{a,b\}$, an oblivious adversary gives reward $0.9$ to the expert picked with probability at most $1/2$, so the regret is at least $0.45$, while $K\sqrt{\Delta\log2}\to0$ as $\Delta\to0$
--   - reading: $O(\sqrt{\Delta T\log|\Gamma|})$, an algorithm $\mathcal A$ → one absolute constant $K_1$ chosen first; the algorithm may depend on $\Delta$, $T$, $\Gamma$; rewards fixed before the coins; reason: C&S configures $\mathcal A$ with $\Gamma$, $T$ and $\Delta=\sigma$ (p.11); the regret puts the benchmark outside the expectation
--   - generalization: $F_t:\Gamma\to[0,1)$ and $T\in\mathbb Z_{>0}$ → $F_t:\Gamma\to[0,1]$ and $T\in\mathbb N$; reason: C&S feeds $F_t(\gamma)=f_t(\cdot)\in[0,1]$; at $T=0$ both sides are $0$; the statement specializes to the source's
--   - encoding: $\log$ → natural logarithm; reason: the base changes only the constant
--   - encoding: the expectation $\mathbb E[\sum_t F_t(\gamma_t)-\Delta\cdot\#\text{switches}]$ → the conclusion also asserts that this random variable is integrable; reason: the source's expectation is that of a bounded random variable; asserting it keeps Lean's value $0$ for a non-integrable function from lowering the regret
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Theorem 3.7, p.10 (citing Kalai and Vempala 2005)

import Mathlib
import Definitions.Def_StatefulPricing_OLSCAlg

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **Theorem 3.7** (Kalai and Vempala (2005); arXiv:2005.01869v2, p.10): "The OLSC problem with
switching cost ∆ admits an online algorithm A whose regret is O(√(∆ · T log |Γ|))."

There is an absolute constant `K₁` such that for every switching cost `Δ ≥ 1`, every horizon `T`
and every finite nonempty expert set `Γ` there is a randomized online algorithm whose regret with
switching cost `Δ` is at most `K₁ √(Δ T log |Γ|)` against every reward sequence with values in
`[0,1]`; the expectation in the regret is that of an integrable random variable.

**Formalization Note.** Integrability is asserted in the conclusion: the integrand contains
`− Δ · #switches`, so Lean's `∫ = 0` for a non-integrable function could otherwise lower the
regret of the witness below its true value. -/
theorem theorem_3_7 :
    ∃ K₁ : ℝ, ∀ Δ : ℝ, 1 ≤ Δ → ∀ (T : ℕ) (ι : Type) [Fintype ι] [Nonempty ι],
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : OLSCAlg Ω ι, A.IsOnline ∧
          ∀ F : ℕ → ι → ℝ, (∀ t, 1 ≤ t → t ≤ T → ∀ j, 0 ≤ F t j ∧ F t j ≤ 1) →
            Integrable (fun ω => (∑ t ∈ Finset.Icc 1 T, F t (A ω t F))
                - Δ * (A.switches ω F T : ℝ)) P ∧
            A.regret P Δ T F ≤ K₁ * Real.sqrt (Δ * T * Real.log (Fintype.card ι)) := by sorry

end StatefulPricing
