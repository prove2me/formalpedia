-- Prove2me | Theorems.Thm_RankOneBTF_claim_6
-- name    : RankOneBTF.claim_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:31.374237+00:00
-- url     : https://prove2.me/theorems/5e97fb48-33b3-4ff9-a36e-03e23eab9d1b
-- title:
--   Claim 6 — inequalities (50) and all counterparts hold strictly w.h.p. (event $A^3$)
-- statement:
--   In the fully-random model with constant $p$, $0<p<r_{\bar w}/(1+2r_{\bar w})$, under the asymptotic regime of Theorem 4, the event $A^3$ that inequalities (50) and all their symmetric counterparts are strictly satisfied,
--   $$
--   \min\Bigl\{T^{x,i}_{11},\frac{T^{x,i}_{111}}{T^{y,z,j,k}_1}\Bigr\}>\frac13F^{x,i}_{00}+\frac12(F^{x,i}_{01}+F^{x,i}_{10})+F^{x,i}_{11}\quad\text{for }(i,j,k)\in\mathcal T,\ \bar x_i=0,\ \bar y_j=\bar z_k=1,
--   $$
--   and the same with $(x,i,n)$ replaced by $(y,j,m)$ and by $(z,k,l)$, occurs with high probability: $\mathbb P[A^3]\to1$.
--
--   Differences from the source:
--   - reading: a claim inside the proof of Theorem 4 → a standalone theorem in the fully-random model with 0 < p and p < r_w̄/(1+2r_w̄); reason: the proof reduces to the fully-random model by Proposition 2 and assumes p > 0 before the claims (p.31)
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances in Theorem4Regime (exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞, the three limit assumptions) the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
--   - encoding: the fractions T^{x,i}_{111}/T^{y,z,j,k}_1 in (50) → real division with a/0 = 0; reason: a vanishing denominator makes the strict inequality false in Lean, so the Lean event is contained in the paper's
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Claim 6, p.33 (event A³ defined p.31)

import Mathlib
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Theorem4Regime
import Definitions.Def_RankOneBTF_Prop10Cond1

open Filter Topology

namespace RankOneBTF

/-- **Claim 6** (arXiv:2202.07053v3, p.33, in the proof of Theorem 4): "Event A³ occurs with
high probability", where A³ is "the event that inequalities (50) and all symmetric counterparts
are strictly satisfied" (p.31).

**Formalization Note** The claim is stated in the fully-random model (the proof of
Theorem 4 begins "By Proposition 2 it suffices to prove the statement under the fully-random
corruption model", p.31) under the hypotheses of Theorem 4 with `p > 0` ("Henceforth, we assume
that p > 0", p.31). "With high probability" is read along sequences (`Theorem4Regime`): the
probability (`frProb`) tends to `1`. -/
theorem claim_6 (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 < p) (hp : p < rx * ry * rz / (1 + 2 * (rx * ry * rz)))
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool) (hreg : Theorem4Regime rx ry rz n m l xb yb zb) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => Ineq50Strict (xb t) (yb t) (zb t) G)) atTop (𝓝 1) := by sorry

end RankOneBTF
