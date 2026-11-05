-- Prove2me | Theorems.Thm_RailwayRM_lemma_2
-- name    : RailwayRM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:21.543347+00:00
-- url     : https://prove2.me/theorems/1fddb629-9cec-48f7-b098-0d966b9be450
-- title:
--   Lemma 2: cost excess of $\pi_1$ (corrected: factor $c_o/k$ on the last sum)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$, with cost $C_D$ as in (10). For every selection of minimizers in step 4 of $\pi_1$,
--   $$C^{\pi_1}_S-C_D\le Mc_o+2M\cdot L\cdot c_s\cdot k+\sum_{m=1}^M\sum_{\ell=1}^L\tfrac12c_s\sqrt{\bar y^*_{\ell,m}(1-\bar y^*_{\ell,m})T}+\sum_{m=1}^M\sum_{\ell=1}^L\frac{c_o}{k}\sqrt{\bar x^*_{\ell,m}(1-\bar x^*_{\ell,m})T}.$$
--
--   This is the cost half of the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - correction: last sum ∑_m ∑_ℓ √(x̄*(1 − x̄*)T) → last sum ∑_m ∑_ℓ (c_o/k) √(x̄*(1 − x̄*)T); reason: (20) carries c_o/k and (21) bounds the expectation alone. Counterexample to the printed form: L = 2, N = 3 (A = leg 1, B = leg 2, C = both), M = 1, δ = 1, T = 100, k = 1, c_o = 10, c_s = 1, b̲ = 0, b̄ = 101, reserved revenue x(6 − 2x) for A and B on [0, 0.3] and x(9 − x) for C on [0, 0.1], unreserved y(0.5 − y) on [0, 0.1]: C^{π1} − C_D = 28.17 exceeds the printed bound 22.66
--   - reading: footnote 2, p. 12: ⌈x⌉ = ⌊x⌋ + 1 → the usual ceiling Nat.ceil; reason: the footnote differs at integers and contradicts the equivalence of (1) and (3), p. 14, and "the minimum number of reserved coaches sufficient", p. 16
--   - reading: E in Q^{π1} (p. 16) → expectation conditional on the observed path, stated for every selection of minimizers; reason: B^{π1} is random and the coaches are chosen at the end of the horizon, so (8) needs the conditional form
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), Lemma 2, App. p. 3, PDF p. 35; (20), App. p. 4, for the factor c_o/k

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **Lemma 2, corrected** (Manchiraju et al., SSRN 4112672 (2023-08-22), Lemma 2, App. p. 3, PDF
p. 35): `C^{π₁}_S - C_D ≤ M c_o + 2 M L c_s k + ∑_m ∑_ℓ ½ c_s √(ȳ*_{ℓ,m}(1 - ȳ*_{ℓ,m}) T)
+ ∑_m ∑_ℓ (c_o/k) √(x̄*_{ℓ,m}(1 - x̄*_{ℓ,m}) T)`.

**Formalization Note.** The factor `c_o/k` on the last sum is the correction: the paper's (20)
carries it and the printed Lemma omits it, and the printed form is false. -/
theorem lemma_2 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b)
    (sel : I.ObsPath → Fin M → ℝ) (hsel : I.IsCapacitySelection v b sel) :
    I.cost (I.pi1 v b sel) - I.detCost v b ≤
      (M : ℝ) * I.co + 2 * (M : ℝ) * (L : ℝ) * I.cs * (I.k : ℝ) +
        ∑ m, ∑ ℓ : Fin L, I.cs / 2 * Real.sqrt (I.ybar v ℓ m * (1 - I.ybar v ℓ m) * (I.T : ℝ)) +
        ∑ m, ∑ ℓ : Fin L, I.co / (I.k : ℝ) *
          Real.sqrt (I.xbar v ℓ m * (1 - I.xbar v ℓ m) * (I.T : ℝ)) := by sorry

end RailwayRM
