-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_proposition_2_9
-- name    : UncertainPricing.Superrep.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:53.482652+00:00
-- url     : https://prove2.me/theorems/49c1e340-cf46-413c-b820-7da718675280
-- title:
--   Proposition 2.9, p. 7 — (B_t − B_s)^{2n} ≤ ∫_s^t h_u dB_u + C μ̄(]s,t])^n q.s., with C depending only on n
-- statement:
--   Let $n\ge0$ be an integer. There is a constant $C>0$, depending only on $n$, with the following property. For every horizon $T>0$, every nonzero measure $\bar\mu$ on $[0,T]$ with continuous distribution function, every set $\mathbf P$ of martingale measures satisfying $H(\bar\mu)$, and all $s\le t$ in $[0,T]$, there is $h\in\mathcal H$ such that
--   $$(B_t-B_s)^{2n}\le\int_s^t h_u\,dB_u+C\,\bar\mu(]s,t])^n\qquad\text{q.s.}$$
--
--   This pathwise, model-free domination of even moments of increments is the source of the moment bound of Proposition 2.13 and, through it, of the Kolmogorov-type continuity arguments of §4–§5.
--
--   **Formalization Note.** $\int_s^t h_u\,dB_u$ is represented as an element of $K_{]s,t]}$: the $c$-limit of integrals of an $\mathcal H$-Cauchy sequence of elementary integrands vanishing outside $]s,t]$. The constant is quantified before $T$, $\bar\mu$, $\mathbf P$, $s$, $t$, since the page says it depends on $n$ only. The page's "$s,t\in[0,T]$" is read with $s\le t$, which the notation $\int_s^t$ and $]s,t]$ presupposes; $n=0$ is allowed (the statement is then trivial).
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Proposition 2.9, p. 7

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem proposition_2_9 (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
        (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
        (s t : Set.Icc (0 : ℝ) T), s ≤ t →
        ∃ g : Ω T → ℝ, InKOn Ps μU s t g ∧
          QS Ps (fun ω => (B t ω - B s ω) ^ (2 * n) ≤ g ω + C * (μU t - μU s) ^ n) := by sorry

end UncertainPricing.Superrep
