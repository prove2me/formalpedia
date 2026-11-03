-- Prove2me | Theorems.Thm_RankOneBTF_claim_5
-- name    : RankOneBTF.claim_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:09.709767+00:00
-- url     : https://prove2.me/theorems/a71f3b1e-fc7e-47ef-b1a1-d0a3b3953d30
-- title:
--   Claim 5 — Condition 2 of Proposition 10 holds w.h.p. for any $0<\alpha<1$ (event $A^2$)
-- statement:
--   In the fully-random model with constant $p$, $0<p<r_{\bar w}/(1+2r_{\bar w})$, under the asymptotic regime of Theorem 4, for any constant $0<\alpha<1$ the event $A^2$ that Condition 2 of Proposition 10 holds,
--   $$
--   T^{x,i}_{111}\ge\alpha T^{x,i}_{11}\bar T^{y,z}_1\ \ (\bar x_i=0),\quad T^{y,j}_{111}\ge\alpha T^{y,j}_{11}\bar T^{x,z}_1\ \ (\bar y_j=0),\quad T^{z,k}_{111}\ge\alpha T^{z,k}_{11}\bar T^{x,y}_1\ \ (\bar z_k=0),
--   $$
--   occurs with high probability: $\mathbb P[A^2]\to1$.
--
--   Differences from the source:
--   - reading: a claim inside the proof of Theorem 4 → a standalone theorem in the fully-random model with 0 < p and p < r_w̄/(1+2r_w̄); reason: the proof reduces to the fully-random model by Proposition 2 and assumes p > 0 before the claims (p.31)
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances in Theorem4Regime (exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞, the three limit assumptions) the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Claim 5, p.32 (event A² defined p.31)

import Mathlib
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Theorem4Regime
import Definitions.Def_RankOneBTF_Prop10Cond1

open Filter Topology

namespace RankOneBTF

/-- **Claim 5** (arXiv:2202.07053v3, p.32, in the proof of Theorem 4): "Event A² occurs with
high probability for any 0 < α < 1", where A² is "the event that Condition 2 of Proposition 10
is satisfied" (p.31).

**Formalization Note** The claim is stated in the fully-random model (the proof of
Theorem 4 begins "By Proposition 2 it suffices to prove the statement under the fully-random
corruption model", p.31) under the hypotheses of Theorem 4 with `p > 0` ("Henceforth, we assume
that p > 0", p.31). "With high probability" is read along sequences (`Theorem4Regime`): the
probability (`frProb`) tends to `1`. -/
theorem claim_5 (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 < p) (hp : p < rx * ry * rz / (1 + 2 * (rx * ry * rz)))
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool) (hreg : Theorem4Regime rx ry rz n m l xb yb zb)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => Prop10Cond2 α (xb t) (yb t) (zb t) G)) atTop (𝓝 1) := by sorry

end RankOneBTF
