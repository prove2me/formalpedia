-- Prove2me | Theorems.Thm_RankOneBTF_claim_4
-- name    : RankOneBTF.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:54.663791+00:00
-- url     : https://prove2.me/theorems/ef250209-e779-4506-bac3-db4064a9e42a
-- title:
--   Claim 4 — Condition 1 of Proposition 10 holds w.h.p. (event $A^1$)
-- statement:
--   In the fully-random model with constant $p$, $0<p<r_{\bar w}/(1+2r_{\bar w})$, under the asymptotic regime of Theorem 4, the event $A^1$ that Condition 1 of Proposition 10 holds ($T^{x,y,i,j}_1\ge1$ whenever $\bar x_i=\bar y_j=1$, and the two symmetric statements) occurs with high probability: $\mathbb P[A^1]\to1$.
--
--   Differences from the source:
--   - reading: a claim inside the proof of Theorem 4 → a standalone theorem in the fully-random model with 0 < p and p < r_w̄/(1+2r_w̄); reason: the proof reduces to the fully-random model by Proposition 2 and assumes p > 0 before the claims (p.31)
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances in Theorem4Regime (exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞, the three limit assumptions) the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Claim 4, p.32 (event A¹ defined p.31)

import Mathlib
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Theorem4Regime
import Definitions.Def_RankOneBTF_Prop10Cond1

open Filter Topology

namespace RankOneBTF

/-- **Claim 4** (arXiv:2202.07053v3, p.32, in the proof of Theorem 4): "Event A¹ occurs with
high probability", where A¹ is "the event that Condition 1 of Proposition 10 is satisfied"
(p.31).

**Formalization Note** The claim is stated in the fully-random model (the proof of
Theorem 4 begins "By Proposition 2 it suffices to prove the statement under the fully-random
corruption model", p.31) under the hypotheses of Theorem 4 with `p > 0` ("Henceforth, we assume
that p > 0", p.31). "With high probability" is read along sequences (`Theorem4Regime`): the
probability (`frProb`) tends to `1`. -/
theorem claim_4 (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 < p) (hp : p < rx * ry * rz / (1 + 2 * (rx * ry * rz)))
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool) (hreg : Theorem4Regime rx ry rz n m l xb yb zb) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => Prop10Cond1 (xb t) (yb t) (zb t) G)) atTop (𝓝 1) := by sorry

end RankOneBTF
