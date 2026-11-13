-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_case_C2
-- name    : RepellingPairs.claim_13_case_C2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:00:33.582741+00:00
-- url     : https://prove2.me/theorems/aae0def2-9697-4242-8329-836b4c9de869
-- title:
--   Claim 13, induction step — case C2, the chord of k does not separate e from C'(k)
-- statement:
--   Same setting as the case C1 and case B statements of the induction in Claim 13 (Chen, Pylyavskyy, Tan, arXiv:2607.02883, p.12), with the configuration packaged as `Ctx13` and `KD` of the bundle `Claim13Aux`: $C\succ C'$, $x,y$ a good pair of minimal segment count, $e$ an end of the arc $S$, and a point $k$ outside the open arc $T$ between $e$ and $C(e)$ with $C(k)\in T$ and $C'(k)\notin T$.
--
--   Case C2: $C(e)$ is not on $S(x)$, the points $x$ and $C'(e)$ are on the same side of the chord $(e,C(e))$, and the chord $(k,C(k))$ does not separate $e$ from $C'(k)$. Then $k,C(e)$ is a good pair, its segment (the one avoiding $C(k)$) lies inside the $x$-$y$ segment avoiding $C(x)$ (the two containment statements `claim_13_case_C2_inside_first` and `claim_13_case_C2_inside_second` cover the two arcs of that segment), and the point $e$ lies on the $x$-$y$ segment but not on the $k$-$C(e)$ segment. So the $k$-$C(e)$ segment is strictly smaller than the $x$-$y$ segment, contradicting minimality:
--
--   $$\mathrm{Ctx13}\wedge\mathrm{KD}\wedge\neg\mathrm{InSegment}(x,C(x),C'(x),C(e))\wedge\neg\mathrm{OnDifferentSides}(e,C(e),x,C'(e))\wedge\neg\mathrm{OnDifferentSides}(k,C(k),e,C'(k))\Longrightarrow\mathrm{False}.$$
--
--   Source: Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, Claim 13, proof, case C2 of the induction step: the chord of k does not separate e from C'(k)

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux

set_option autoImplicit false

namespace RepellingPairs
theorem claim_13_case_C2 {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k)) : False := by sorry

end RepellingPairs
