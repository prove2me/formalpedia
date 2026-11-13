-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_case_C2_inside_first
-- name    : RepellingPairs.claim_13_case_C2_inside_first
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:00:50.95555+00:00
-- url     : https://prove2.me/theorems/ba783458-36ea-4146-9aff-19a8252bb4fa
-- title:
--   Claim 13, induction step — case C2, points between C(k) and C(e) lie on the x-y segment
-- statement:
--   Same setting as the case C1 statement of the induction in Claim 13 (Chen, Pylyavskyy, Tan, arXiv:2607.02883, p.12), with the configuration packaged as `Ctx13` and `KD` of the bundle `Claim13Aux`: $C\succ C'$, $x,y$ a good pair of minimal segment count, $e$ an end of the arc $S$, and a point $k$ outside the open arc $T$ between $e$ and $C(e)$ with $C(k)\in T$ and $C'(k)\notin T$.
--
--   Case C2: the chord $(k,C(k))$ does not separate $e$ from $C'(k)$. Then the pair $k,e$ is a good pair, and by minimality of $x,y$ its segment cannot be strictly smaller than the $x$-$y$ segment. This statement is the first half of the resulting containment: every point $a$ strictly between $C(k)$ and $C(e)$ (cyclic order $C(k),k,a,C(e)$) lies on the $x$-$y$ segment avoiding $C(x)$.
--
--   $$a\ \text{with}\ (C(k),k,a,C(e))\ \text{cyclically ordered}\ \Longrightarrow\ (C(x),x,a,y)\ \text{or}\ (C(x),y,a,x)\ \text{cyclically ordered}.$$
--
--   Source: Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, Claim 13, proof, last case of the induction step: points between C(k) and C(e) lie on the x-y segment

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux

set_option autoImplicit false

namespace RepellingPairs

theorem claim_13_case_C2_inside_first {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : ¬ OnDifferentSides k (C.partner k) e (C'.partner k))
    (a : Fin n) (ha : CyclicallyOrdered (C.partner k) k a (C.partner e)) :
    (CyclicallyOrdered (C.partner x) x a y ∨ CyclicallyOrdered (C.partner x) y a x) := by sorry

end RepellingPairs
