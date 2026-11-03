-- Prove2me | Theorems.Thm_RankOneBTF_claim_7
-- name    : RankOneBTF.claim_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:44.231934+00:00
-- url     : https://prove2.me/theorems/d2718884-49f4-4a17-9ccd-176642d68dcf
-- title:
--   Claim 7 — inequalities (51) hold strictly w.h.p. (event $A^4$)
-- statement:
--   In the fully-random model with constant $p>0$, under the asymptotic regime of Theorem 4, let $0<\alpha<1$ satisfy
--   $$
--   p<\frac{\alpha\,r_{\bar x}r_{\bar y}r_{\bar z}}{1+(3\alpha-1)\,r_{\bar x}r_{\bar y}r_{\bar z}}.\qquad(83)
--   $$
--   Then, with high probability, $T^{x,i}_{11}>0$ for every $i$ with $\bar x_i=0$ (likewise $T^{y,j}_{11}$, $T^{z,k}_{11}$), and the event $A^4$ that inequalities (51) are strictly satisfied,
--   $$
--   3\bar\gamma_{ijk}>\max\Bigl\{\frac{F^{x,i}_{11}}{T^{x,i}_{11}},\frac{F^{y,j}_{11}}{T^{y,j}_{11}},\frac{F^{z,k}_{11}}{T^{z,k}_{11}}\Bigr\}\qquad\text{for all }(i,j,k)\in\mathcal T\cap\mathcal P,
--   $$
--   occurs with $\bar\gamma_{ijk}$ computed with this $\alpha$.
--
--   Condition (83) holds for some $\alpha<1$ whenever (20) does, and implies (20).
--
--   Differences from the source:
--   - reading: "Event A⁴ occurs with high probability", with α left implicit (the proof fixes α < 1 with (83), which exists by (20)) → for every α ∈ (0,1) satisfying (83); hypothesis (20) is not stated separately; reason: the proof uses exactly (83) (p.36); (83) implies (20)
--   - reading: the strict inequalities (51), whose sums divide by T^{x,i′}_{11}, T^{y,j′}_{11}, T^{z,k′}_{11} → the event also requires these counts to be positive for every zero coordinate; reason: the paper's (51) presupposes its denominators are nonzero; the conjunct keeps Lean's a/0 = 0 from enlarging the event
--   - reading: a claim inside the proof of Theorem 4 → a standalone theorem in the fully-random model with 0 < p; reason: the proof reduces to the fully-random model by Proposition 2 and assumes p > 0 before the claims (p.31)
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances in Theorem4Regime (exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞, the three limit assumptions) the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Claim 7, p.35 (event A⁴ defined p.31; condition (83), p.36)

import Mathlib
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Theorem4Regime
import Definitions.Def_RankOneBTF_gammaBar

open Filter Topology

namespace RankOneBTF

/-- **Claim 7** (arXiv:2202.07053v3, p.35, in the proof of Theorem 4): "Event A⁴ occurs with
high probability", where A⁴ is "the event that inequalities (51) are strictly satisfied"
(p.31). The proof (p.36) fixes `α < 1` with
`p < α r_x̄ r_ȳ r_z̄ / (1 + (3α − 1) r_x̄ r_ȳ r_z̄)` (83), which exists by (20).

**Formalization Note** The claim is stated in the fully-random model (the proof of
Theorem 4 begins "By Proposition 2 it suffices to prove the statement under the fully-random
corruption model", p.31) under the hypotheses of Theorem 4 with `p > 0` ("Henceforth, we assume
that p > 0", p.31). "With high probability" is read along sequences (`Theorem4Regime`): the
probability (`frProb`) tends to `1`. The claim is stated for every `α ∈ (0,1)`
satisfying (83) (which implies (20)). The event also requires `T^{x,i'}_{11} > 0` for every
`i'` with `x̄_{i'} = 0` (and likewise for `y`, `z`): these are the denominators of the sums in
`γ̄_ijk`, which the paper's (51) presupposes to be nonzero; with them, Lean's `a / 0 = 0` cannot
make the event easier. -/
theorem claim_7 (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 < p) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h83 : p < α * (rx * ry * rz) / (1 + (3 * α - 1) * (rx * ry * rz)))
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool) (hreg : Theorem4Regime rx ry rz n m l xb yb zb) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => (∀ i, xb t i = false → 0 < Tx (xb t) (yb t) (zb t) G true true i) ∧
          (∀ j, yb t j = false → 0 < Ty (xb t) (yb t) (zb t) G true true j) ∧
          (∀ k, zb t k = false → 0 < Tz (xb t) (yb t) (zb t) G true true k) ∧
          Ineq51Strict α (xb t) (yb t) (zb t) G)) atTop (𝓝 1) := by sorry

end RankOneBTF
