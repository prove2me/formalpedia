-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_Supplement_theorem_3
-- name    : WaitTimePricing.Existence.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:42:12.960658+00:00
-- url     : https://prove2.me/theorems/328d01d6-1545-4d38-81e8-1d9fa488fce9
-- title:
--   Theorem 3 (corrected: policy equality P* = p*_s, and counterexample to the closed rejection interval)
-- statement:
--   For every model satisfying the standing assumptions and for both revenue and social welfare, with $V=V^{\bar g}$ the constructed relative value function, the service-based pricing decision (35)–(38) agrees with the price feedback (26):
--   $$P^*(w)=p^*_s(w)\qquad\text{for all }w\in[0,\bar w].$$
--
--   The printed five-section threshold conclusion, however, is false under the printed acceptance convention. Take revenue with
--   $$U(t)=2t-t^2/2,\qquad c(w)=w,\qquad C=1,\qquad\lambda=1/100.$$
--   These primitives satisfy the published standing assumptions. The constructed rate satisfies $0<g<1$, and $\hat w=1/2$, $\bar w=3/2$. Put $r=3/2-g$, so $\hat w<r<\bar w$. The source's policy (35)–(39) has
--   $$P^*(r)=g,\qquad T^*(r)=1,\qquad T^*(w)=0\quad(r<w\le\bar w).$$
--   The service argmax is a singleton for every $w\in[0,\hat w]$. Consequently there are no thresholds satisfying the full printed conclusion, including its closed rejection interval $[W_3,\bar w]$. All the original policy definitions and the entire ten-clause conclusion are preserved in the definition of that conclusion. The statement gives an exact counterexample, rather than assuming a favorable load or moving an endpoint without disclosure.
--
--   Differences from the source:
--   - encoding: Assumption 1 and positive arrival and service primitives → the immutable base Standing predicate, including global C³/C² extensions and λ,C>0; reason: reuse of the published model; inequalities remain on their original physical domains
--   - correction: universal five-section threshold conclusion with rejection on the closed interval [W3,wbar] → the policy equality P*=p*_s stated for every standing model and both objectives, plus an exact admissible revenue model refuting the threshold conclusion, with admission at r and rejection strictly above r; reason: (37) admits at zero optimized value; at r=3/2−g its optimized value is exactly zero, precluding both the printed fourth and fifth service clauses for every W3
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 21, Theorem 3; pp. 20–21, (35)–(39); pp. 51–53, Appendix D

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Supplement_ServicePolicy

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 21, Theorem 3, with (35)–(39), pp. 20–21.
Formalization Note: counterexample to the printed closed rejection interval, without changing
(35)–(39). Set U(t)=2t−t²/2, c(w)=w, C=1, λ=1/100, revenue. Then ŵ=1/2, wbar=3/2,
0<g<1, and r=3/2−g is strictly above ŵ. At r the acceptance expression is exactly zero,
so (37) admits service 1, while every w in (r,wbar] rejects. No W3 can give both the printed
fourth and fifth service clauses. `FiveSections` retains policy equality, all thresholds and
all ten printed clauses on the full intervals. No load or regularity premise has been added.
The first conjunct states the theorem's opening clause, P*(w) = p*_s(w) on [0,wbar], for every
model satisfying the standing assumptions and both concrete objectives: the counterexample refutes
only the threshold clause, so the policy-equality clause is kept at full strength.
The threshold clause is replaced by an explicit counterexample as required by the source-audit policy. -/
theorem theorem_3 :
    (∀ (M : Model) (obj : Objective), M.Standing →
      ∀ w ∈ Icc 0 (wbar M),
        PStar M obj w = feedback M (concreteReward M obj) (Vbar M obj) w) ∧
    let M := testModel (1 / 100)
    let g := gbar M .revenue
    let r := (3 : ℝ) / 2 - g
    M.Standing ∧ what M = 1 / 2 ∧ wbar M = 3 / 2 ∧
    0 < g ∧ g < 1 ∧ what M < r ∧ r < wbar M ∧
    (∀ w ∈ Icc 0 (what M), ∃ t : ℝ, serviceArgmax M .revenue w = {t}) ∧
    PStar M .revenue r = g ∧ TStar M .revenue r = 1 ∧
    (∀ w ∈ Ioc r (wbar M), TStar M .revenue w = 0) ∧
    ¬ FiveSections M .revenue := by sorry

end WaitTimePricing.Existence.Supplement
