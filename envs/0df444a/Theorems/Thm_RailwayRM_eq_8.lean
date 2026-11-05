-- Prove2me | Theorems.Thm_RailwayRM_eq_8
-- name    : RailwayRM.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:27.726033+00:00
-- url     : https://prove2.me/theorems/3e8985e9-9539-417c-90d8-15fe0e8bfdda
-- title:
--   (8): $C^{\pi_1}_S\le C^{\tilde\pi_1}_U+M\cdot L\cdot c_s\cdot k$
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$. For every selection of minimizers in step 4 of $\pi_1$, the expected cost $C^{\pi_1}_S$ of $\pi_1$ and the expected cost $C^{\tilde\pi_1}_U$ of the relaxed policy, given by (9), satisfy
--   $$C^{\pi_1}_S\le C^{\tilde\pi_1}_U+M\cdot L\cdot c_s\cdot k.$$
--
--   This compares the stopped policy with the relaxed one path by path, on one probability space.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - reading: footnote 2, p. 12: ⌈x⌉ = ⌊x⌋ + 1 → the usual ceiling Nat.ceil; reason: the footnote differs at integers and contradicts the equivalence of (1) and (3), p. 14, and "the minimum number of reserved coaches sufficient", p. 16
--   - reading: E in Q^{π1} (p. 16) → expectation conditional on the observed path, stated for every selection of minimizers; reason: B^{π1} is random and the coaches are chosen at the end of the horizon, so (8) needs the conditional form
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (8), App. p. 3, PDF p. 35; (9), App. p. 3

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **(8)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (8), App. p. 3, PDF p. 35):
`C^{π₁}_S ≤ C^{π̃₁}_U + M · L · c_s · k`, for every selection of minimizers in step 4 of `π₁`.

**Formalization Note.** `C^{π̃₁}_U` of (9) is `cost` of `relaxedPolicy`. The correction
`b*_{u,m} < b̄_m` of Lemma 1 is not needed here: a train with `b*_{u,m} = b̄_m` has `x̄*_{ℓ,m} = 0`,
and `⌊b*_{u,m}⌋` still lies in the box of step 4 on every path of positive probability. -/
theorem eq_8 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b)
    (sel : I.ObsPath → Fin M → ℝ) (hsel : I.IsCapacitySelection v b sel) :
    I.cost (I.pi1 v b sel) ≤
      I.cost (I.relaxedPolicy v b) + (M : ℝ) * (L : ℝ) * I.cs * (I.k : ℝ) := by sorry

end RailwayRM
