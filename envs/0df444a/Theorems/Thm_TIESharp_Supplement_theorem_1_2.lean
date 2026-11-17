-- Prove2me | Theorems.Thm_TIESharp_Supplement_theorem_1_2
-- name    : TIESharp.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:56:26.548527+00:00
-- url     : https://prove2.me/theorems/ca7345cd-b06e-4eec-80eb-fa1a58e6302a
-- title:
--   Theorem 1.2 — $5/2\le\rho(4)\le3$, $3\le\rho(5)\le105/32$, $7/2\le\rho(6)\le29/8$
-- statement:
--   For $n$ machines let $\rho(n)$ be the optimal truthful-in-expectation approximation ratio for makespan minimization on unrelated machines: the infimum of all $R$ for which some feasible, truthful-in-expectation mechanism family on $n$ machines has expected makespan at most $R\cdot\mathrm{OPT}(t)$ at truthful reports, for every number of jobs $m\ge0$ and every nonnegative processing-time matrix $t$. Then
--
--   $$\frac52\le\rho(4)\le3,\qquad 3\le\rho(5)\le\frac{105}{32},\qquad \frac72\le\rho(6)\le\frac{29}{8}.$$
--
--   The lower bounds are the general bound $\rho(n)\ge(n+1)/2$ at $n=4,5,6$; the upper bounds come from the Bounded-Square mechanism with slot rounding. Together with Theorem 1.1 ($\rho(n)=(n+1)/2$ for $n\ge7$) this leaves the exact values only for four, five and six machines open.
--
--   **Formalization Note** $\rho(n)$ is the published `TIESharp.rho`, an infimum on $\mathbb R$. The lower bounds exclude the junk value $0$ of an empty or unbounded-below set, so the statement is about the true infimum.
--
--   Differences from the source: none.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 1.2, p.2 (PDF p.3); proof p.12 (PDF p.13); ρ(n) defined §2, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_TIESharp_rho

set_option autoImplicit false

namespace TIESharp

namespace Supplement

/-- **Theorem 1.2 (Four, five, and six machines)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Theorem 1.2, p.2; proof p.12). The optimal truthful-in-expectation
approximation ratios satisfy `5/2 ≤ ρ(4) ≤ 3`, `3 ≤ ρ(5) ≤ 105/32` and `7/2 ≤ ρ(6) ≤ 29/8`.

**Formalization Note.** `ρ(n)` is the published `TIESharp.rho n`, the `sInf` on `ℝ` of all `R`
for which some feasible, truthful-in-expectation family on `n` machines is `R`-approximate
(uniformly over all job counts `m ≥ 0` and all nonnegative profiles). The lower bounds force the
set to be nonempty and bounded below (otherwise `sInf` would be the junk value `0 < 5/2`), so no
junk value of `sInf` satisfies the statement. -/
theorem theorem_1_2 :
    (5 / 2 : ℝ) ≤ rho 4 ∧ rho 4 ≤ 3 ∧
    (3 : ℝ) ≤ rho 5 ∧ rho 5 ≤ 105 / 32 ∧
    (7 / 2 : ℝ) ≤ rho 6 ∧ rho 6 ≤ 29 / 8 := by sorry

end Supplement

end TIESharp
