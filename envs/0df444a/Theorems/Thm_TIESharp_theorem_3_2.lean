-- Prove2me | Theorems.Thm_TIESharp_theorem_3_2
-- name    : TIESharp.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:40.325727+00:00
-- url     : https://prove2.me/theorems/ad677139-99c7-4499-b368-fe69b4af1ce1
-- title:
--   Theorem 3.2 — unrestricted lower bound $R\ge(n+1)/2$ for every $n\ge1$
-- statement:
--   For every $n\ge1$, any truthful-in-expectation family with a finite approximation ratio $R$ uniform over all finite job counts satisfies
--   $$R\ \ge\ \frac{n+1}{2}.$$
--   The family may correlate job assignments arbitrarily and need not be measurable or computable. In particular $\rho(n)\ge(n+1)/2$.
--
--   Differences from the source:
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Theorem 3.2, p.5

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox

set_option autoImplicit false

namespace TIESharp

/-- **Theorem 3.2 (Unrestricted lower bound)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Theorem 3.2, p.5). For every `n ≥ 1`, any truthful-in-expectation
family with a finite approximation ratio `R` uniform over all finite job counts satisfies
`R ≥ (n + 1)/2`.

**Formalization Note.** The family is any `Family n` that is feasible (assignment distributions),
truthful in expectation (2.1) and `R`-approximate (2.2) for every job count; no measurability,
continuity, column-locality or independence across jobs is assumed. -/
theorem theorem_3_2 (n : ℕ) (hn : 1 ≤ n) (F : Family n) (R : ℝ) (hF : IsFeasible F)
    (hT : IsTIE F) (hR : IsRApprox F R) : ((n : ℝ) + 1) / 2 ≤ R := by sorry

end TIESharp
