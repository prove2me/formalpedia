-- Prove2me | Theorems.Thm_QVolKLS_lemma_6_2
-- name    : QVolKLS.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:41.920808+00:00
-- url     : https://prove2.me/theorems/19e15588-d01d-4918-9770-19ff75c08f0e
-- title:
--   Lemma 6.2 — second moments along cooling are at most $2$ (continuous) and $4$ (lattice)
-- statement:
--   Let $d\ge2$, $D=d+1$, $\kappa>0$, and let $K\subseteq\mathbb R^d$ be a convex body with $B(0,1)\subseteq K\subseteq B(0,\kappa)$. Let $a_i$ be the cooling schedule (54), $m$ its length, $\Delta=a_i/(16\lceil\sqrt d\rceil)$, $\pi_a$ the continuous laws $\propto e^{-ax_0}$ on the pencil $K_0$, and $\pi_i$ the lattice laws on $K_0\cap h\mathbb Z^D$.
--
--   1. For every $0\le i<m$,
--   $$
--   \mathbb E_{\pi_{a_i}}\!\big[(\pi_{a_{i+1}}/\pi_{a_i})^2\big]\le2,\qquad \mathbb E_{\pi_{a_{i+1}}}\!\big[(\pi_{a_i}/\pi_{a_{i+1}})^2\big]\le2 .
--   $$
--   2. For every spacing $h>0$ and $0\le i<m$: if
--   $$
--   \tfrac{99}{100}Z(a)\le Z_\Lambda(a)\le\tfrac{101}{100}Z(a)\qquad\text{for } a\in\{a_i-2\Delta,\ a_i-\Delta,\ a_i,\ a_i+\Delta\},
--   $$
--   then both finite relative second moments $\sum_z\pi_{i+1}(z)^2/\pi_i(z)$ and $\sum_z\pi_i(z)^2/\pi_{i+1}(z)$ are at most $4$.
--   3. There is one dyadic spacing $h>0$, depending only on $d$ and $\kappa$, at which these approximations hold for every such body $K$, every $i<m$ and all four values of $a$.
--
--   Bounded relative second moments give constant overlap of adjacent qsamples and let one preconditioner serve two consecutive stages.
--
--   Differences from the source:
--   - encoding: §6.1 standing assumptions: 'Assume d ≥ 2 below' (p.44) and the rescaled body B(0,1) ⊆ K ⊆ B(0,κ) → hypotheses d ≥ 2, IsConvexBody K, Metric.ball 0 1 ⊆ K ⊆ Metric.closedBall 0 κ; reason: they restate the section's setting; balls as in the main theorem
--   - generalization: the finite moments are bounded on 'a dyadic lattice' satisfying the approximations → clause 2 holds for every spacing h > 0 satisfying the approximations; reason: the implication does not use dyadicity; it specializes to dyadic h
--   - reading: we can choose a dyadic lattice such that … → one dyadic h chosen from d and κ before K; reason: the stronger reading; the proof chooses h from the schedule and the geometric bounds through Theorem 5.2 (iv) and Lemma B.2, which are uniform in K
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 6.2, p.46 (with (54), p.46; (47), p.45)

import Definitions.Def_QVolKLS_pencil

set_option autoImplicit false

namespace QVolKLS

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 6.2 (Second moments along
cooling)**, p.46. Standing assumptions of §6.1 (p.44): `d ≥ 2`, and the body is rescaled so that
`B(0, 1) ⊆ K ⊆ B(0, κ)`; `K₀` is the pencil, `a_i` the schedule (54), `m` its length.

1. For every `0 ≤ i < m`, both continuous relative second moments
   `E_{π_{a_i}}[(π_{a_{i+1}}/π_{a_i})²]` and `E_{π_{a_{i+1}}}[(π_{a_i}/π_{a_{i+1}})²]` are at most `2`.
2. For every lattice spacing `h > 0` and `i < m`: if `(99/100) Z(a) ≤ Z_Λ(a) ≤ (101/100) Z(a)` at the
   four points `a ∈ {a_i − 2∆, a_i − ∆, a_i, a_i + ∆}`, `∆ = a_i/(16⌈√d⌉)`, then both finite relative
   second moments of `π_i`, `π_{i+1}` are at most `4`.
3. There is a dyadic spacing `h > 0` at which these approximations hold for every `i < m` and all four
   points (one lattice for every body `K` with the standing bounds).

**Formalization Note.** Moments are written from their definitions (`contRelMoment`,
`finRelMoment`); `π_i` is the lattice law at `a_i` on `K₀ ∩ hℤ^D`. In clause 3 the spacing is chosen
from `d` and `κ` before `K`. -/
theorem lemma_6_2 (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) :
    (∀ K : Set (Euc d), IsConvexBody K → Metric.ball 0 1 ⊆ K → K ⊆ Metric.closedBall 0 κ →
      ∀ i < coolingLength d κ,
        contRelMoment K κ (coolingA d i) (coolingA d (i + 1)) ≤ 2 ∧
        contRelMoment K κ (coolingA d (i + 1)) (coolingA d i) ≤ 2) ∧
    (∀ K : Set (Euc d), IsConvexBody K → Metric.ball 0 1 ⊆ K → K ⊆ Metric.closedBall 0 κ →
      ∀ h : ℝ, 0 < h → ∀ i < coolingLength d κ,
        (∀ a ∈ ({coolingA d i - 2 * coolingDelta d i, coolingA d i - coolingDelta d i,
            coolingA d i, coolingA d i + coolingDelta d i} : Set ℝ),
          99 / 100 * pencilZ K κ a ≤ pencilZLat K κ h a ∧
            pencilZLat K κ h a ≤ 101 / 100 * pencilZ K κ a) →
        finRelMoment K κ h (coolingA d i) (coolingA d (i + 1)) ≤ 4 ∧
        finRelMoment K κ h (coolingA d (i + 1)) (coolingA d i) ≤ 4) ∧
    (∃ h : ℝ, 0 < h ∧ IsDyadic h ∧
      ∀ K : Set (Euc d), IsConvexBody K → Metric.ball 0 1 ⊆ K → K ⊆ Metric.closedBall 0 κ →
        ∀ i < coolingLength d κ,
          ∀ a ∈ ({coolingA d i - 2 * coolingDelta d i, coolingA d i - coolingDelta d i,
              coolingA d i, coolingA d i + coolingDelta d i} : Set ℝ),
            99 / 100 * pencilZ K κ a ≤ pencilZLat K κ h a ∧
              pencilZLat K κ h a ≤ 101 / 100 * pencilZ K κ a) := by sorry

end QVolKLS
