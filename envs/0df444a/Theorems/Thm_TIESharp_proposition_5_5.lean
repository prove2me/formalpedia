-- Prove2me | Theorems.Thm_TIESharp_proposition_5_5
-- name    : TIESharp.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:26.552448+00:00
-- url     : https://prove2.me/theorems/fc6968dd-878f-41ce-83cc-7bd1145c7cb7
-- title:
--   Proposition 5.5 — seven machines: expected makespan at most $4\,\mathrm{OPT}$
-- statement:
--   The Bounded-Square slot mechanism has expected makespan at most $4\,\mathrm{OPT}$ on seven machines, for every finite job count and all finite nonnegative processing times:
--   $$\sum_A y_A\,C_{\max}(t,A)\le4\,\mathrm{OPT}(t).$$
--   Together with Theorem 3.2 this gives $\rho(7)=4$.
--
--   Differences from the source:
--   - generalization: the Bounded-Square slot mechanism → every slot-rounding law of the Bounded-Square probabilities (IsBSSlotLaw); reason: the mechanism's law is one; the paper's bounds hold for every decomposition (p.23)
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Proposition 5.5, p.25

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

namespace TIESharp

/-- **Proposition 5.5 (Seven machines)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Proposition 5.5, p.25). The Bounded-Square slot mechanism has
expected makespan at most `4 OPT` on seven machines, for every finite job count and all finite
nonnegative processing times.

**Formalization Note.** Machines are `Fin 7`; the mechanism's assignment law is any slot-rounding
law of the Bounded-Square probabilities (`IsBSSlotLaw`), which contains every decomposition of
Sec. 5.2. `OPT(t) = 0` is included. -/
theorem proposition_5_5 (m : ℕ) (t : Fin 7 → Fin m → ℝ) (ht : Nonneg t)
    (y : (Fin m → Fin 7) → ℝ) (hy : IsBSSlotLaw t y) :
    ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 4 * opt t := by sorry

end TIESharp
