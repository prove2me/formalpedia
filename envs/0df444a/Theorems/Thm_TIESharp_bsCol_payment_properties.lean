-- Prove2me | Theorems.Thm_TIESharp_bsCol_payment_properties
-- name    : TIESharp.bsCol_payment_properties
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:30.92962+00:00
-- url     : https://prove2.me/theorems/8f2bf777-3ebc-4b1a-88f0-9197e5985e5b
-- title:
--   Bounded-Square marginals: normalization, monotonicity, and payment integrability
-- statement:
--   Let $c\in[0,\infty)^n$ be one job's processing-time column, with $n\ge2$. Its Bounded-Square probabilities $q_i(c)$ are nonnegative and sum to one. For each machine $i$, the function
--   $$s\longmapsto q_i(c_{-i},s)$$
--   is nonincreasing on $[0,\infty)$ and integrable on $(0,\infty)$, hence also on every tail $(s,\infty)$ with $s\ge0$.
--
--   The monotonicity includes jumps when competitors become eligible, the cutoff beyond which the probability is zero, and zero-cost ties. Integrability supplies the finiteness required by the expected-payment formula.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, §5.2, 'Monotonicity, including the cutoff points' and 'Apply the payment lemma', p.23.

import Mathlib
import Definitions.Def_TIESharp_bsCol

set_option autoImplicit false

/-- The Bounded-Square one-job probabilities satisfy the hypotheses of the payment lemma,
including at eligibility cutoffs and zero-cost ties (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §5.2, p.23). -/
theorem TIESharp.bsCol_payment_properties (n : ℕ) (hn : 2 ≤ n)
    (c : Fin n → ℝ) (hc : ∀ a, 0 ≤ c a) (i : Fin n) :
    0 ≤ TIESharp.bsCol c i ∧ (∑ k, TIESharp.bsCol c k) = 1 ∧
    AntitoneOn (fun s => TIESharp.bsCol (Function.update c i s) i) (Set.Ici 0) ∧
    MeasureTheory.IntegrableOn (fun u => TIESharp.bsCol (Function.update c i u) i) (Set.Ioi 0) ∧
    ∀ s : ℝ, 0 ≤ s →
      MeasureTheory.IntegrableOn (fun u => TIESharp.bsCol (Function.update c i u) i) (Set.Ioi s) := by sorry
