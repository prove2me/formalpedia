-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_case_C1
-- name    : RepellingPairs.claim_13_case_C1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:00:21.099167+00:00
-- url     : https://prove2.me/theorems/0ad2ed71-85f1-495b-b422-b330815d4747
-- title:
--   Claim 13, induction step — case C1, the chord of k separates e from C'(k)
-- statement:
--   Let $C,C'$ be perfect matchings on the boundary points $\mathbb Z/n$ with $C\succ C'$, and let $x,y$ be a good pair whose $x$-$y$ segment avoiding $C(x)$ has the fewest points among all good pairs. In the induction proving Claim 13, the step for a point $e$ at an end of the arc $S$ of points containing $x$ and $C'(x)$ and avoiding $y$ and $C(x)$ requires ruling out $C(e)\in S$, $C'(e)\notin S$. The proof picks the open arc $T$ with endpoints $e$ and $C(e)$ that contains $C'(e)$; since $\mathrm{dist}_{C'}(T)\le \mathrm{dist}_C(T)$, there is a point $k\notin T$ with $C(k)\in T$ and $C'(k)\notin T$.
--
--   This statement is the case in which the chord $(k,C(k))$ separates $e$ from $C'(k)$. Under the hypotheses of the induction step (the bundle `Claim13Aux` packages them as `Ctx13` and `KD`; the statement also assumes that $C(e)$ is not on the segment $S(x)$ from $C(x)$ to $C'(x)$ and that $x$ and $C'(e)$ do not lie on different sides of the chord $(e,C(e))$, the outcomes of the earlier cases), the pair $k,e$ is then a good pair whose segment is strictly smaller than that of $x,y$, contradicting minimality. So the hypotheses are inconsistent:
--
--   $$\text{(Ctx13 and KD hypotheses, and } k \text{ separates } e \text{ from } C'(k)) \Longrightarrow \mathrm{False}.$$
--
--   Source: Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12, the final case of the induction along the bars between $x$ and $y$.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, Claim 13, proof, last case of the induction step: the chord of k separates e from C'(k)

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Definitions.Def_Claim13Aux

set_option autoImplicit false

namespace RepellingPairs

theorem claim_13_case_C1 {n : ℕ} (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e u v k : Fin n)
    (K : Claim13Aux.Ctx13 C C' x y s m e)
    (hA : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner e))
    (hB : ¬ OnDifferentSides e (C.partner e) x (C'.partner e))
    (D : Claim13Aux.KD C C' e u v k)
    (hk : OnDifferentSides k (C.partner k) e (C'.partner k)) : False := by sorry

end RepellingPairs
