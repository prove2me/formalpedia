-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_case_C2_inside_second
-- name    : RepellingPairs.claim_13_case_C2_inside_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:00:18.039197+00:00
-- url     : https://prove2.me/theorems/49c828aa-0c1f-4a92-bf9d-27295f9949be
-- title:
--   Claim 13, induction step — case C2, points between C(e) and k lie on the x-y segment
-- statement:
--   Same setting as the first half of case C2 (Chen, Pylyavskyy, Tan, arXiv:2607.02883, p.12, Claim 13), with the configuration packaged as `Ctx13` and `KD` of the bundle `Claim13Aux`: $C\succ C'$, $x,y$ a good pair of minimal segment count, $e$ an end of the arc $S$, and a point $k$ outside the open arc $T$ between $e$ and $C(e)$ with $C(k)\in T$ and $C'(k)\notin T$, where the chord $(k,C(k))$ does not separate $e$ from $C'(k)$.
--
--   This statement is the second half of the containment used to show that the pair $k,e$ cannot have a smaller segment than $x,y$ unless it already lies inside the $x$-$y$ segment: every point $a$ strictly between $C(e)$ and $k$ (cyclic order $C(k),C(e),a,k$) lies on the $x$-$y$ segment avoiding $C(x)$.
--
--   $$a\ \text{with}\ (C(k),C(e),a,k)\ \text{cyclically ordered}\ \Longrightarrow\ (C(x),x,a,y)\ \text{or}\ (C(x),y,a,x)\ \text{cyclically ordered}.$$
--
--   Source: Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, Claim 13, proof, last case of the induction step: points between C(e) and k lie on the x-y segment

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux

set_option autoImplicit false

namespace RepellingPairs

theorem claim_13_case_C2_inside_second {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) (C.partner e) a k) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) := by sorry

end RepellingPairs
