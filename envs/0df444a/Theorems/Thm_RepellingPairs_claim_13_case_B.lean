-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_case_B
-- name    : RepellingPairs.claim_13_case_B
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:01:06.589666+00:00
-- url     : https://prove2.me/theorems/870f0a23-cfba-4d00-b302-e11d7648f4fc
-- title:
--   Claim 13, induction step — case B, the chord (e, C(e)) separates x from C'(e)
-- statement:
--   Let $C,C'$ be perfect matchings on the boundary points $\mathbb Z/n$ with $C\succ C'$, and let $x,y$ be a good pair whose $x$-$y$ segment avoiding $C(x)$ has the fewest points among all good pairs. In the induction proving Claim 13, the step for a point $e$ at an end of the arc $S$ of points containing $x$ and $C'(x)$ and avoiding $y$ and $C(x)$ requires ruling out $C(e)\in S$, $C'(e)\notin S$ (the bundle `Claim13Aux` packages the standing assumptions as `Ctx13`).
--
--   This statement is the case in which $C(e)$ does not lie on the segment $S(x)$ from $C(x)$ to $C'(x)$ and the chord $(e,C(e))$ separates $x$ from $C'(e)$. Then $e,x$ is a good pair whose segment is strictly smaller than that of $x,y$, contradicting minimality, so the hypotheses are inconsistent:
--
--   $$\mathrm{Ctx13}\ \wedge\ \neg\,\mathrm{InSegment}(x,C(x),C'(x),C(e))\ \wedge\ \mathrm{OnDifferentSides}(e,C(e),x,C'(e))\ \Longrightarrow\ \mathrm{False}.$$
--
--   Source: Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12, the case analysis of the induction along the bars between $x$ and $y$.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, Claim 13, proof, case B of the induction step: the chord of e separates x from C'(e)

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux

set_option autoImplicit false

namespace RepellingPairs
theorem claim_13_case_B {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : OnDifferentSides e (C.partner e) x (C'.partner e)) : False := by sorry

end RepellingPairs
