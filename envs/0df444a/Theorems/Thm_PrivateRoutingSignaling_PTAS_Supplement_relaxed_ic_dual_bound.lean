-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_Supplement_relaxed_ic_dual_bound
-- name    : PrivateRoutingSignaling.PTAS.Supplement.relaxed_ic_dual_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:01.895666+00:00
-- url     : https://prove2.me/theorems/34bd58d4-a2ff-4e77-b60f-cf3ba9b29a7f
-- title:
--   Lemma 2.1 — relaxed-IC schemes cost at least the dual value minus $\varepsilon$ times the maximum row sum
-- statement:
--   Let an instance satisfy the standing assumptions of §2.1: a network with at least one simple source–sink path, a nonempty finite set of states $\Theta$ with prior $\lambda$, and arc latencies $c_i^\theta$ that are nonnegative, nondecreasing and continuous on $[0,1]$. Let $Y=(Y_{p,q})_{p\neq q}$ be any nonnegative dual matrix, let $\varepsilon\ge0$, and let $\varphi$ be a signaling scheme, that is, a Borel probability measure on $\Theta\times\Delta_P$ with state marginal $\lambda$, satisfying the $\varepsilon$-relaxed IC constraints
--
--   $$
--   \sum_\theta\sum_{s\in\Delta_P}\varphi(\theta,s)\,s_p\bigl[c_q^\theta(s)+\varepsilon-c_p^\theta(s)\bigr]\ge0\qquad\text{for all }p,q\in P,\ p\neq q.
--   $$
--
--   Then
--
--   $$
--   \mathrm{SC}(\varphi)\ \ge\ \sum_\theta\lambda_\theta D^\theta(Y)-\varepsilon\max_{p\in P}\sum_{q\neq p}Y_{p,q}.
--   $$
--
--   The lemma shows that relaxing incentive compatibility by $\varepsilon$ lowers the attainable social cost by at most $\varepsilon$ times the largest row sum of any dual certificate. It turns the hardness of exact-IC approximation into hardness of bicriteria approximation in Theorems 4.9, 5.7 and 6.8.
--
--   **Formalization Note** Sums against $\varphi$ are Bochner integrals for an arbitrary Borel scheme over real flows; the IC terms carry the probability weight $s_p$ inside the integrand. $D^\theta(Y)$ is the infimum over all real flows. No Lipschitz bound is assumed.
--
--   Differences from the source:
--   - reading: ε-relaxed IC constraints with an unrestricted ε → ε ≥ 0; reason: ε is a tolerance of drivers (§2.3, p. 8), and for ε < 0 the printed bound is false: two parallel paths, two states of prior 1/2 with constant latencies (c_1, c_2) = (0, M) and (M, 0), φ routing everything on path 1 in the first state and on path 2 in the second, Y_{1,2} = 1, Y_{2,1} = 0 and ε = −M satisfy both relaxed constraints with equality, while SC(φ) = 0 < M/2 = ∑_θ λ_θ D^θ(Y) − ε·1
--   - encoding: Y = (Y_{p,q})_{p≠q} → a matrix on all ordered pairs of paths whose diagonal is never read; reason: the dummy zero diagonal of §2.2 (p. 7)
--   - encoding: sums over s ∈ Δ_P against φ → integrals against a Borel probability measure on states × real flows; reason: the summation notation of §2.1 (p. 6) for general distributions
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), Lemma 2.1, p. 8 (PDF p. 8); proof p. 9; standing assumptions §2.1 p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_Dual

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- Lemma 2.1 (Cheng–Jiang, STOC 2027 submission #439, p. 8; proof p. 9). For every
nonnegative dual matrix `Y`, every tolerance `ε ≥ 0` and every Borel scheme with the prior that
satisfies the (probability-weighted) `ε`-relaxed IC constraints,
`SC(φ) ≥ ∑_θ λ_θ D^θ(Y) − ε max_p ∑_{q≠p} Y_{p,q}`. -/
theorem relaxed_ic_dual_bound (I : Instance) (hI : ContinuousSetting I)
    (Y : DualMatrix I.network) (hY : DualNonneg Y) (ε : ℝ) (hε : 0 ≤ ε)
    (φ : Scheme I) (hφ : IsScheme I φ) (hob : Obedient I ε φ) :
    ∑ θ, I.prior θ * dualValue I θ Y - ε * maxRowSum Y ≤ socialCost I φ := by sorry

end PrivateRoutingSignaling.PTAS.Supplement
