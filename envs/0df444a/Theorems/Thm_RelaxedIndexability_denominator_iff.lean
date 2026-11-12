-- Prove2me | Theorems.Thm_RelaxedIndexability_denominator_iff
-- name    : RelaxedIndexability.denominator_iff
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:22:00.772959+00:00
-- url     : https://prove2.me/theorems/cdafd2b4-1584-4298-981b-e510e49e2f27
-- title:
--   Remark after Theorem 3 — condition (40) holds iff the denominator of (41) is nonzero
-- statement:
--   Let an arm have a row-stochastic transition matrix $\mathbf P$ with rows $p_0,\dots,p_{K-1}$ and rewards $B$, let $0<\beta<1$, and let the belief $\omega$ be fixed as a point in the threshold. Write $\hat D_\beta$ for the passive time of the threshold policy and $f, g, F(\mathbf P), H(\mathbf P)$ as in (41). Then the denominator of the approximated Whittle index (41) is the difference of the $m$-slopes of the two sides of (37):
--   $$
--   1 + \beta f(\omega\mathbf P) + \beta\big[\beta g(\omega\mathbf P) - \omega\big] H(\mathbf P) F(\mathbf P) = 1 + \beta \hat D_\beta(\mathcal T^1(\omega)) - \beta\,\omega\big(\hat D_\beta(p_0), \dots, \hat D_\beta(p_{K-1})\big)',
--   $$
--   and consequently the relaxed indexability condition (40),
--   $$
--   \beta\,\omega\big(\hat D_\beta(p_0), \dots, \hat D_\beta(p_{K-1})\big)' \ne 1 + \beta \hat D_\beta(\mathcal T^1(\omega)),
--   $$
--   holds if and only if that denominator is nonzero.
--
--   Differences from the source:
--   - generalization: (40) ⇔ the denominator of (41) is nonzero → adds the identity: the denominator equals 1 + βD̂_β(T¹(ω)) − βω(D̂_β(p₀),…,D̂_β(p_{K−1}))′; reason: the identity implies the equivalence, which is stated as the second clause.
--   - generalization: the standing assumptions P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: not used; the statement for every row-stochastic P and every B contains the source's case.
--   - encoding: the passive time D̂_{β,m} → passiveTime without an m argument; reason: the threshold rule (33) does not involve m, so D̂_{β,m} = D̂_β for every m (stated on p.22).
--   - reading: L(·,ω) = +∞ in f and g → β^{+∞} = 0, so f = 1/(1−β) and g = 0; reason: β^{+∞} = lim βⁿ = 0, as Algorithm 1 uses.
--   - encoding: D̂ is the expected total discounted passive time under π_{β,m} → the limit of the n-horizon expected discounted passive times (reward 1 passive, 0 active) computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Remark after Theorem 3, first bullet, p.23

import Mathlib
import Definitions.Def_RelaxedIndexability_passiveTime
import Definitions.Def_RelaxedIndexability_approxWhittle

open Matrix

namespace RelaxedIndexability

/-- **Condition (40) is the nonvanishing of the denominator of (41)** (Liu, arXiv:2107.11939v4,
Remark after Theorem 3, first bullet, p.23). Fix `ω` in the simplex as a point in the threshold.
The denominator of (41) equals the difference of the `m`-slopes of the two sides of (37):

`1 + βf(ωP) + β[βg(ωP) − ω]H(P)F(P) = 1 + βD̂_β(T¹(ω)) − βω(D̂_β(p₀), …, D̂_β(p_{K−1}))′`,

and hence (40), `βω(D̂_β(p₀), …, D̂_β(p_{K−1}))′ ≠ 1 + βD̂_β(T¹(ω))`, holds iff that denominator is
nonzero. -/
theorem denominator_iff {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) :
    whittleDenominator β P B ω =
        1 + β * passiveTime β P B ω (ω ᵥ* P) - β * (ω ⬝ᵥ fun k => passiveTime β P B ω (P k)) ∧
    (β * (ω ⬝ᵥ fun k => passiveTime β P B ω (P k)) ≠ 1 + β * passiveTime β P B ω (ω ᵥ* P) ↔
      whittleDenominator β P B ω ≠ 0) := by sorry

end RelaxedIndexability
