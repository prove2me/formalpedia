-- Prove2me | Theorems.Thm_RankOneBTF_flowerLP_recovers_whp_semiRandom
-- name    : RankOneBTF.flowerLP_recovers_whp_semiRandom
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:43.68283+00:00
-- url     : https://prove2.me/theorems/b1497bfb-9d8c-47db-81a4-c947d6b688c4
-- title:
--   Theorem 4 — the flower LP recovers the planted rank-one tensor w.h.p. under semi-random corruption when $p<r_{\bar w}/(1+2r_{\bar w})$
-- statement:
--   Let $r_{\bar x},r_{\bar y},r_{\bar z}>0$ be constants, $r_{\bar w}:=r_{\bar x}r_{\bar y}r_{\bar z}$, and let $p\ge0$ be a constant with
--   $$
--   p<\frac{r_{\bar w}}{1+2r_{\bar w}}.\qquad(20)
--   $$
--   Consider any sequence of instances $(n_t,m_t,l_t,\bar x_t,\bar y_t,\bar z_t)$ in which $\bar x_t$ has exactly $r_{\bar x}n_t$ ones (likewise $\bar y_t$, $\bar z_t$), $n_t,m_t,l_t\to\infty$ and
--   $$
--   n_tm_tl_te^{-n_t}\to0,\qquad n_tm_tl_te^{-m_t}\to0,\qquad n_tm_tl_te^{-l_t}\to0 ,
--   $$
--   and any sequence of semi-random adversaries. Draw the noisy tensor $\mathcal G$ from $\bar{\mathcal W}_t=\bar x_t\otimes\bar y_t\otimes\bar z_t$ by corrupting each entry independently with probability $p$, and let the adversary revert any subset of the corrupted entries (chosen as a function of $\mathcal G$) to their true values. Then the probability that the flower LP (fLP) built from the modified tensor has $(\bar x_t,\bar y_t,\bar z_t,\bar{\mathcal W}_t)$ as its **unique** optimal solution tends to $1$.
--
--   This is the main result of the paper: adding the flower inequalities to the standard LP raises the corruption level up to which exact recovery is guaranteed from about $r_{\bar w}/(2(1+r_{\bar w}))$ (Corollary 1) to $r_{\bar w}/(1+2r_{\bar w})$, and the guarantee survives a monotone adversary.
--
--   **Formalization Note** The probability is an explicit finite sum over corruption patterns with Bernoulli($p$) weights (`frProb`); the adversary is any map whose output agrees entrywise with its input or with $\bar{\mathcal W}_t$ (`IsMonotoneAdversary`). $p=0$ is included.
--
--   Differences from the source:
--   - reading: "with high probability" as n, m, l → ∞ with constant ratios → for every sequence of instances in Theorem4Regime (exact ratios r_x̄, r_ȳ, r_z̄, sizes → ∞, the three limit assumptions) the probability tends to 1; reason: p.3 defines w.h.p. as probability → 1 as n, m, l → ∞; quantifying over all such sequences is the only precise reading and the strongest
--   - encoding: an adversary applying an arbitrary sequence of monotone transformations → any map adv with adv G i j k ∈ {G i j k, W̄ i j k} for every entry; reason: a sequence of reversions changes exactly a (G-dependent) subset of corrupted entries back to W̄; same instances
--   - encoding: probability under i.i.d. corruptions with probability p ∈ [0,1] → finite sum over corruption patterns of Π p^{C}(1−p)^{1−C}, with 0 ≤ p (p ≤ 1 follows from (20)); reason: same probability space
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §4.3, Theorem 4, p.10, (20)

import Mathlib
import Definitions.Def_RankOneBTF_flpRegion
import Definitions.Def_RankOneBTF_frProb
import Definitions.Def_RankOneBTF_Theorem4Regime

open Filter Topology

namespace RankOneBTF

/-- **Theorem 4** (Del Pia, Khajavirad, *Rank-one Boolean tensor factorization and the
multilinear polytope*, arXiv:2202.07053v3, §4.3, p.10): "Consider the semi-random corruption
model. Assume that r_x̄, r_ȳ, r_z̄ are positive constants and let r_w̄ := r_x̄ r_ȳ r_z̄. Assume
that, as n, m, l → ∞, we have nml exp(−n), nml exp(−m), nml exp(−l) → 0. If p is a constant
satisfying p < r_w̄/(1 + 2r_w̄) (20), then Problem (fLP) recovers the ground truth with high
probability."

**Formalization Note** "With high probability" is read along sequences (`Theorem4Regime`):
for every sequence of sizes and ground truths with exact ratios `r_x̄, r_ȳ, r_z̄`, sizes tending
to infinity and the three limit assumptions, and every sequence of semi-random adversaries
`adv t`, the probability that (fLP) built from the adversarially modified tensor `adv t G` has
`(x̄_t, ȳ_t, z̄_t, W̄_t)` as its unique optimal solution tends to `1`. `G` is drawn from the
fully-random model with parameter `p` (i.i.d. Bernoulli(`p`) corruptions; `frProb`). `p` is a
probability, so `0 ≤ p`; `p = 0` is included. -/
theorem flowerLP_recovers_whp_semiRandom (rx ry rz p : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hrz : 0 < rz) (hp0 : 0 ≤ p) (hp : p < rx * ry * rz / (1 + 2 * (rx * ry * rz)))
    (n m l : ℕ → ℕ) (xb : ∀ t, Fin (n t) → Bool) (yb : ∀ t, Fin (m t) → Bool)
    (zb : ∀ t, Fin (l t) → Bool) (hreg : Theorem4Regime rx ry rz n m l xb yb zb)
    (adv : ∀ t, BTensor (n t) (m t) (l t) → BTensor (n t) (m t) (l t))
    (hadv : ∀ t, IsMonotoneAdversary (groundTruth (xb t) (yb t) (zb t)) (adv t)) :
    Tendsto (fun t => frProb p (groundTruth (xb t) (yb t) (zb t))
        (fun G => FLPRecovers (adv t G) (xb t) (yb t) (zb t))) atTop (𝓝 1) := by sorry

end RankOneBTF
