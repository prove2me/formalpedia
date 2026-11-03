-- Prove2me | Theorems.Thm_RankOneBTF_claim_1
-- name    : RankOneBTF.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:15.254486+00:00
-- url     : https://prove2.me/theorems/492a7bc7-b22e-4427-9bff-cb27fe75c5e9
-- title:
--   Claim 1 — Condition 1 of Proposition 7 holds w.h.p.
-- statement:
--   In the fully-random model with a constant $0<p\le1$, and under the assumptions of Theorem 3 other than its threshold (exact constant ratios $r_{\bar x},r_{\bar y},r_{\bar z}>0$, $n,m,l\to\infty$, and $n e^{-m}, n e^{-l}, m e^{-n}, m e^{-l}, l e^{-n}, l e^{-m}\to0$), the event $A^0$ that Condition 1 of Proposition 7 holds — every $i$ with $\bar x_i=0$ has $F^{x,i}>0$, and likewise for $y$, $z$ — occurs with high probability:
--   $$
--   \mathbb P[A^0]\to1 .
--   $$
--
--   The proof of Theorem 4 invokes it as "By proof of Claim 1, Condition 1 of Proposition 7 holds with high probability"; Theorem 4's limit assumptions ($nml\,e^{-n}, nml\,e^{-m}, nml\,e^{-l}\to0$) imply Theorem 3's, so the statement covers that use.
--
--   Differences from the source:
--   - reading: Claim 1 inside the proof of Theorem 3 → a standalone theorem in the fully-random model with p > 0; reason: the proof of Theorem 3 reduces to the fully-random model by Proposition 2 and assumes p > 0 before the claims (p.20)
--   - generalization: Theorem 3's hypotheses, including threshold (19) and the ordering r_x̄ ≥ r_ȳ ≥ r_z̄ → Theorem 3's hypotheses without (19) and without the ordering, with 0 < p ≤ 1; reason: the proof of the claim uses only p > 0 (with (38), Hoeffding and the limit assumptions); every p allowed by (19) satisfies 0 < p < 1/2, so the printed case is included
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances with exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞ and Theorem 3's six limit assumptions, the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §7.2, Claim 1, p.20 (in the proof of Theorem 3); used in the proof of Theorem 4, p.31

import Mathlib
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Prop7Cond1

open Filter Topology

namespace RankOneBTF

/-- **Claim 1** (arXiv:2202.07053v3, p.20, in the proof of Theorem 3): "Event A⁰ occurs with
high probability", where "A⁰ [is] the event that Condition 1 in Proposition 7 is satisfied".
The proof of Theorem 4 uses it: "By proof of Claim 1, Condition 1 of Proposition 7 holds with
high probability" (p.31).

**Formalization Note** The claim is stated in the fully-random model (the proof of Theorem 3
begins "By Proposition 2 it suffices to prove the statement under the fully-random corruption
model", p.20) with `p > 0` ("Henceforth, suppose that p > 0", p.20), under the hypotheses of
Theorem 3 (p.9): positive constant ratios `r_x̄, r_ȳ, r_z̄` (exact: `|{i : x̄_i = 1}| = r_x̄ n`),
`n, m, l → ∞`, and `n exp(−m), n exp(−l), m exp(−n), m exp(−l), l exp(−n), l exp(−m) → 0`.
Threshold (19) and the ordering `r_x̄ ≥ r_ȳ ≥ r_z̄` of Theorem 3 are not assumed (the proof of the
claim uses only `p > 0`); `p ≤ 1` is assumed instead, so that `p` is a probability. Theorem 4's
limit assumptions imply Theorem 3's, so the claim covers its use in the proof of Theorem 4.
"With high probability" is read along sequences: the probability (`frProb`) tends to `1`
along every sequence of instances satisfying these assumptions. -/
theorem claim_1 (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool)
    (hx : ∀ t, numOnes (xb t) = rx * (n t : ℝ)) (hy : ∀ t, numOnes (yb t) = ry * (m t : ℝ))
    (hz : ∀ t, numOnes (zb t) = rz * (l t : ℝ))
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop) (hl : Tendsto l atTop atTop)
    (hnm : Tendsto (fun t => (n t : ℝ) * Real.exp (-(m t : ℝ))) atTop (𝓝 0))
    (hnl : Tendsto (fun t => (n t : ℝ) * Real.exp (-(l t : ℝ))) atTop (𝓝 0))
    (hmn : Tendsto (fun t => (m t : ℝ) * Real.exp (-(n t : ℝ))) atTop (𝓝 0))
    (hml : Tendsto (fun t => (m t : ℝ) * Real.exp (-(l t : ℝ))) atTop (𝓝 0))
    (hln : Tendsto (fun t => (l t : ℝ) * Real.exp (-(n t : ℝ))) atTop (𝓝 0))
    (hlm : Tendsto (fun t => (l t : ℝ) * Real.exp (-(m t : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => Prop7Cond1 (xb t) (yb t) (zb t) G)) atTop (𝓝 1) := by sorry

end RankOneBTF
