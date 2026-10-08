-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_theorem10
-- name    : SongZipkinFluct.Monotone.theorem10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:49.819974+00:00
-- url     : https://prove2.me/theorems/a2ed0180-13cd-4d13-be22-05252a70c583
-- title:
--   Theorem 10 — with K > 0, the bounds S⁺(i), r⁺(i), r⁻(i), r⁻⁻(i) are nondecreasing in the world state
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 and Condition 1 for a partial order $\preceq$ on the world states, and a positive fixed order cost $K = \bar K\,\tilde F_L(\alpha) > 0$. Let $y^+(i)$, $y^*(i)$, $y^+_{\min}$ and
--   $$S^+(i),\quad r^+(i),\quad r^-(i),\quad r^{--}(i)$$
--   be as defined on p. 358 of the paper (see the definition `Bounds`). These numbers exist, and each of $S^+$, $r^+$, $r^-$, $r^{--}$ is nondecreasing in $i$: $i \preceq j$ implies $S^+(i) \le S^+(j)$, and likewise for the others.
--
--   The paper could not show that the optimal $(r,S)$ parameters $r^*(i)$, $S^*(i)$ are themselves monotone. Since $y^*(i) \le S^*(i) < S^+(i)$ and $r^{--}(i) \le r^-(i) \le r^*(i) \le r^+(i)$ (Theorem 6), Theorem 10 shows that the optimal policy cannot depart far from monotonicity.
--
--   **Formalization Note.** The statement first asserts that all seven quantities exist, then that every such choice of them is nondecreasing.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 360–361, §4.3, Theorem 10 (definitions p. 358)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1
import Definitions.Def_SongZipkinFluct_Monotone_Bounds

namespace SongZipkinFluct.Monotone

/-- **Theorem 10** (Song and Zipkin 1993, §4.3, pp. 360–361): with a positive fixed order cost
`K > 0`, "Under condition 1, `S⁺(i)`, `r⁺(i)`, `r⁻(i)`, and `r⁻⁻(i)` are all nondecreasing in
`i`."

**Formalization Note.** `S⁺, r⁺, r⁻, r⁻⁻` are characterized by `Model.IsBounds` (p. 358). The
statement first asserts that they exist, then that every such choice is nondecreasing for `⪯`. -/
theorem theorem10 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1)
    (hK : 0 < M.K) :
    (∃ (yplus ystar : I → ℤ) (ymin : ℤ) (Splus rplus rminus rminus2 : I → ℤ),
      M.IsBounds yplus ystar ymin Splus rplus rminus rminus2) ∧
    ∀ (yplus ystar : I → ℤ) (ymin : ℤ) (Splus rplus rminus rminus2 : I → ℤ),
      M.IsBounds yplus ystar ymin Splus rplus rminus rminus2 →
      Monotone Splus ∧ Monotone rplus ∧ Monotone rminus ∧ Monotone rminus2 := by sorry

end SongZipkinFluct.Monotone
