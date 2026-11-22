-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_2_4
-- name    : SamplingLLL.Supplement.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:56:19.313794+00:00
-- url     : https://prove2.me/theorems/e58a949d-a6fa-401d-a059-7f1b6bcc2539
-- title:
--   Theorem 2.4, p.8 — radius-two endpoint: FPRAS and perfect sampler under $8pQ\le1$, $O(|A|)$ expected recursive calls
-- statement:
--   Let a product-space CSP with exact one-event access satisfy $\lambda(\mathrm{Bad}_a)\le p$ for every $a\in A$, where $Q$ is the radius-two volume of the dependency graph $H$. If
--   $$
--   8pQ\le 1, \tag{R2}
--   $$
--   then, for absolute constants $C$, $d$, $K$ chosen before the instance:
--
--   1. $Z>0$;
--   2. the sampler of Appendix H terminates almost surely and its output law is exactly $\mu$;
--   3. its expected number of constraint evaluations, its expected number of one-event-access calls and its remaining expected bit cost are each at most $C(L+1)^d$, where $L$ is the input length;
--   4. across all insertions its expected number of recursive calls is at most $C\,|A|$;
--   5. for every rational $\varepsilon\in(0,1]$ the FPRAS terminates, uses at most $C\,((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ evaluations, access calls and remaining bit operations on every run, and outputs $\hat Z$ with $(1-\varepsilon)Z\le\hat Z\le(1+\varepsilon)Z$ with probability at least $3/4$.
--
--   This is the endpoint of the radius-two local-lemma condition for general (not necessarily atomic) events: counting and exact sampling need only evaluation and one-event access.
--
--   **Formalization Note** The CSP has real coordinate laws (`RCSP`); the oracles of one-event access and their exactness are `Access` and `Access.Exact`. The sampler and FPRAS are `RCSP.r2Sampler` and `RCSP.r2Fpras`. The real $p$ is not an argument of any procedure: the algorithm runs at $p=1/(8Q)$. Recursive calls, evaluations and access calls are read off the call counter with the weights `CW.recW`, `CW.evalW`, `CW.accW`.
--
--   Differences from the source:
--   - reading: "$Z$ has an FPRAS and $\mu$ has an expected-polynomial-time perfect sampler" → the clauses are stated for the explicit procedures `r2Sampler` and `r2Fpras` of Appendix H, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - encoding: exact one-event access: evaluation, exact draws from $\lambda_v$ and from $\lambda(\cdot\mid\mathrm{Bad}_a)$ in expected polynomial time, $\lambda(\mathrm{Bad}_a)$ an exactly computable rational of polynomial encoding length → oracle arguments with exact laws whose calls are counted, and the rationals $\lambda(\mathrm{Bad}_a)$ supplied as input and counted in the input length; reason: the theorem bounds the numbers of calls and the remaining work separately, so the cost of the oracles themselves does not enter; same instances
--   - reading: "The numbers of evaluation and one-event-access calls, and the degrees of all remaining polynomial running-time bounds, are universal" → expected evaluations, expected access calls and expected remaining ticks of the sampler are each at most $C(L+1)^d$ with $C,d$ absolute; for the FPRAS the same three quantities are at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ on every run; reason: the sentence gives no explicit form; this is the form of the published Theorem 2.6, with one absolute degree for all bounds
--   - reading: "has an FPRAS" → for every rational $\varepsilon\in(0,1]$: termination, relative error $\varepsilon$ with probability at least $3/4$, worst-case cost polynomial in $L$, $\ell(\varepsilon)$ and $1/\varepsilon$ under the work cap of p.25; reason: the standard meaning, with the success probability and cap of the proof (p.25) and the bit length of the rational $\varepsilon$ in the input
--   - encoding: $\mu$ is assumed to exist → $Z>0$ is a stated conclusion; reason: the conditional law requires $Z>0$, which the proof establishes
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.4 and Definition 2.3, p.8; proof in Appendix H, pp.70–72

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_r2Data

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc RCSP

/-- Theorem 2.4 (Radius-two endpoint), p.8. Let a product-space CSP with exact one-event access satisfy
`λ(Bad_a) ≤ p` for every `a`, and `8pQ ≤ 1` (R2). Then `Z > 0`; the sampler of Appendix H terminates almost
surely with law exactly `μ`; its expected numbers of constraint evaluations and of one-event-access calls,
and its remaining expected work, are at most `C (L+1)^d`; its expected number of recursive calls across all
insertions is at most `C |A|`; and for every rational `ε ∈ (0,1]` the FPRAS has relative error `ε` with
probability at least `3/4`, with worst-case work, evaluations and access calls at most
`C ((L + bits ε + 1) ⌈1/ε⌉)^d`. The constants `C`, `d`, `K` are absolute.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.4 and Definition 2.3,
p.8; proof in Appendix H, pp.70–72.

**Formalization Note.** The clauses are about the explicit procedures `r2Sampler` and `r2Fpras` (Appendix H
on the packet circuit and scalar factory of Appendix A), not about programs chosen by `∃`. Exact
one-event access is a set of oracles (`Access`, `Access.Exact`): an oracle's own running time is not in the
counters, and each oracle call and each constraint evaluation is one unit of the call counter under the
weights `CW.accW`, `CW.evalW` (and one tick for issuing it). The remaining work is the tick counter, under
the base charge table. `p` is real and is not an argument of any procedure: the algorithm runs at the
endpoint `p = 1/(8Q)` (p.70). `L = inputSize` (variables, domain sizes, scopes, and the rationals
`λ(Bad_a)`). The coordinate laws are real; Definition 2.3 does not require them to be rational. -/
theorem theorem_2_4 : ∃ C d K : ℕ, ∀ {n m : ℕ} (P : RCSP n m) (O : P.Access) (p : ℝ),
    O.Exact → (∀ a, P.prob (P.bad a) ≤ p) → 8 * p * (P.Q : ℝ) ≤ 1 →
    0 < P.Z ∧
    mass (P.r2Sampler O CW.recW) = 1 ∧
    (∀ y, law (P.r2Sampler O CW.recW) y = ENNReal.ofReal (P.mu y)) ∧
    expTicks (P.r2Sampler O CW.recW) ≤ ((C * (P.inputSize O + 1) ^ d : ℕ) : ℝ≥0∞) ∧
    expCalls (P.r2Sampler O CW.evalW) ≤ ((C * (P.inputSize O + 1) ^ d : ℕ) : ℝ≥0∞) ∧
    expCalls (P.r2Sampler O CW.accW) ≤ ((C * (P.inputSize O + 1) ^ d : ℕ) : ℝ≥0∞) ∧
    expCalls (P.r2Sampler O CW.recW) ≤ ((C * m : ℕ) : ℝ≥0∞) ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      mass (P.r2Fpras O CW.recW K d ε) = 1 ∧
      (∀ w ∈ [CW.recW, CW.evalW, CW.accW], ∀ r, P.r2Fpras O w K d ε r ≠ 0 →
        r.2.1 ≤ C * ((P.inputSize O + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d ∧
        (w ≠ CW.recW → r.2.2 ≤ C * ((P.inputSize O + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d)) ∧
      (3 / 4 : ℝ≥0∞) ≤ probOf (P.r2Fpras O CW.recW K d ε) fun Zh =>
        (1 - (ε : ℝ)) * P.Z ≤ (Zh : ℝ) ∧ (Zh : ℝ) ≤ (1 + (ε : ℝ)) * P.Z := by sorry

end SamplingLLL.Supplement
