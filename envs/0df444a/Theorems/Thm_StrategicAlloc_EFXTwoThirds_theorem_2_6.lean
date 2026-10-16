-- Prove2me | Theorems.Thm_StrategicAlloc_EFXTwoThirds_theorem_2_6
-- name    : StrategicAlloc.EFXTwoThirds.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T15:58:40.533555+00:00
-- url     : https://prove2.me/theorems/2c2e03ca-d6f7-4d2d-a7fb-97774c5fadd6
-- title:
--   Theorem 2.6 — for two agents every EFX allocation is 2/3-MMS
-- statement:
--   Let two agents have additive valuations $v_1,v_2$ with non-negative values over a finite set $M$ of goods, and let $\mu_i$ denote agent $i$'s maximin share for two bundles. If $(A_1,A_2)$ is an allocation of $M$ that is EFX (only goods of positive value to the envious agent are removed), then
--
--   $$v_i(A_i)\ \ge\ \tfrac23\,\mu_i\qquad\text{for } i=1,2.$$
--
--   This is the worst-case maximin-share guarantee of an EFX allocation for two agents, which the paper attributes to Proposition 3.3 of Amanatidis, Birmpas and Markakis. Theorem 4.7 shows that equilibria of always-EFX mechanisms do strictly better than this generic bound.
--
--   **Formalization Note** The tightness sentence after Theorem 2.6 ("for every $\delta>0$ there exists an EFX allocation that is not $(2/3+\delta)$-MMS") is not part of this statement.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 5, Theorem 2.6

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

namespace StrategicAlloc.EFXTwoThirds

/-- Theorem 2.6 (p. 5): for two agents with additive non-negative valuations, every EFX
allocation is a 2/3-MMS allocation. -/
theorem theorem_2_6 {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A) :
    StrategicAlloc.EFXFour.IsApproxMMS (2 / 3) v A := by sorry

end StrategicAlloc.EFXTwoThirds
