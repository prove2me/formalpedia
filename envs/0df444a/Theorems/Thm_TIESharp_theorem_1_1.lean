-- Prove2me | Theorems.Thm_TIESharp_theorem_1_1
-- name    : TIESharp.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:11.746708+00:00
-- url     : https://prove2.me/theorems/8f4337a7-3d83-4312-a67a-ac2fbb172272
-- title:
--   Theorem 1.1 — optimal ratio for $n\ge7$ machines: $\rho(n)=(n+1)/2$, attained
-- statement:
--   The optimal approximation ratio of truthful-in-expectation scheduling on $n\ge7$ unrelated machines is
--   $$\rho(n)=\frac{n+1}{2},$$
--   and the infimum is attained: some feasible truthful-in-expectation family is $\frac{n+1}{2}$-approximate, uniformly over all finite job counts.
--
--   Here $\rho(n)$ is the infimum of the ratios $R$ of feasible, truthful-in-expectation families that are $R$-approximate for every job count and every nonnegative profile; the families may correlate jobs arbitrarily and need not be measurable.
--
--   Differences from the source:
--   - generalization: ρ(n) = (n+1)/2 → ρ(n) = (n+1)/2 and some feasible TIE family is (n+1)/2-approximate; reason: §1.1 ("give a mechanism that attains it") and p.2 ("The mechanism in Section 3.2 attains the lower bound for n ≥ 7"); it implies the printed equality
--   - encoding: ρ(n) as an infimum over TIE families with finite uniform ratio → rho n = sInf of real R with a feasible, IsTIE, IsRApprox family; reason: Lean convention; attainment rules out the empty-set junk value
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Theorem 1.1, p.2; attainment from §1.1, p.1 and the remark after Theorem 1.1, p.2

import Mathlib
import Definitions.Def_TIESharp_rho

set_option autoImplicit false

namespace TIESharp

/-- **Theorem 1.1 (Optimal ratio for at least seven machines)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Theorem 1.1, p.2). The optimal approximation
ratio of truthful-in-expectation scheduling on `n ≥ 7` unrelated machines is
`ρ(n) = (n + 1)/2`; moreover the infimum is attained: some feasible truthful-in-expectation family
is `(n + 1)/2`-approximate ("For n ≥ 7, we determine ρ(n) and give a mechanism that attains it",
§1.1, p.1).

**Formalization Note.** `ρ(n)` is `rho n`, the `sInf` over all real `R` for which a feasible,
truthful-in-expectation, `R`-approximate family exists (uniform over all job counts `m ≥ 0` and all
nonnegative profiles). The attainment conjunct makes the set nonempty, so the equality is not a
junk value of `sInf`. -/
theorem theorem_1_1 (n : ℕ) (hn : 7 ≤ n) :
    rho n = ((n : ℝ) + 1) / 2 ∧
      ∃ F : Family n, IsFeasible F ∧ IsTIE F ∧ IsRApprox F (((n : ℝ) + 1) / 2) := by sorry

end TIESharp
