-- Prove2me | Theorems.Thm_RailwayRM_eq_11
-- name    : RailwayRM.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:10.217097+00:00
-- url     : https://prove2.me/theorems/d083e29f-0485-40e0-bf1b-a38942eb31ce
-- title:
--   (11): $C^{\pi_1}_{S,\kappa}-C_{D,\kappa}=O(\sqrt\kappa)$ (corrected: the two-sided bound needs $b^*_{u,m}<\bar b_m$)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$. With $\pi_1$ built in the $\kappa$-scaled system from $(\vec x^*,\vec y^*,\kappa\vec b^*_u)$:
--
--   1. there is a constant $C$ such that for every integer $\kappa\ge1$ and every selection of minimizers, $C^{\pi_1}_{S,\kappa}-C_{D,\kappa}\le C\sqrt\kappa$;
--   2. if $b^*_{u,m}<\bar b_m$ for all $m$, there is a constant $C$ such that for every integer $\kappa\ge1$ and every selection,
--   $$\big|C^{\pi_1}_{S,\kappa}-C_{D,\kappa}\big|\le C\sqrt\kappa.$$
--
--   The first clause is what the proof of Theorem 2 uses. The second is the two-sided reading of $O(\sqrt\kappa)$.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - reading: "the capacities are all scaled by κ" (p. 17) → b̄_m and b̲_m both scale by κ; reason: App. p. 6 says the solution of P_{D,κ} is (x⃗*, y⃗*, κb⃗*_u), which fails if b̲_m does not scale and binds
--   - reading: footnote 2, p. 12: ⌈x⌉ = ⌊x⌋ + 1 → the usual ceiling Nat.ceil; reason: the footnote differs at integers and contradicts the equivalence of (1) and (3), p. 14, and "the minimum number of reserved coaches sufficient", p. 16
--   - reading: E in Q^{π1} (p. 16) → expectation conditional on the observed path, stated for every selection of minimizers; reason: B^{π1} is random and the coaches are chosen at the end of the horizon, so (8) needs the conditional form
--   - correction: O(√κ) with no condition on b*_{u,m} → the upper bound with no condition, and the two-sided bound under b*_{u,m} < b̄_m for every m; reason: in the instance of the corrected Theorem 2, π1 stops after period 1, so its cost stays bounded in κ while C_{D,κ} = 1.5κ, and the difference is linear and negative
--   - encoding: O(√κ) in κ ∈ ℕ → ∃ C, ∀ κ ≥ 1 (κ : ℕ+), |·| ≤ C √κ; reason: the bound holds for every κ ≥ 1, not only eventually; C comes before κ
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (11), App. p. 3, PDF p. 35

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **(11)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (11), App. p. 3, PDF p. 35):
`C^{π₁}_{S,κ} - C_{D,κ} = O(√κ)`. The constant `C` comes before `κ` and the selection.

**Formalization Note.** `C_{D,κ}` is `detCost` of the `κ`-scaled instance at `(x⃗*, y⃗*, κ b⃗*_u)`.
The first clause is the upper bound, which is what the proof gives, and it needs no extra hypothesis.
The second clause is the two-sided `O(√κ)`. It carries the hypothesis `b*_{u,m} < b̄_m`, because at
`b*_{u,m} = b̄_m` the policy can stop selling after period 1 and its cost can fall below `C_{D,κ}` by
an amount linear in `κ`. -/
theorem eq_11 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) :
    (∃ C : ℝ, ∀ (κ : ℕ+) (sel : (I.scale κ).ObsPath → Fin M → ℝ),
      (I.scale κ).IsCapacitySelection v (scaleCoaches κ b) sel →
        (I.scale κ).cost ((I.scale κ).pi1 v (scaleCoaches κ b) sel) -
            (I.scale κ).detCost v (scaleCoaches κ b) ≤ C * Real.sqrt ((κ : ℕ) : ℝ)) ∧
    ((∀ m, b m < (I.bMax m : ℝ)) →
      ∃ C : ℝ, ∀ (κ : ℕ+) (sel : (I.scale κ).ObsPath → Fin M → ℝ),
        (I.scale κ).IsCapacitySelection v (scaleCoaches κ b) sel →
          |(I.scale κ).cost ((I.scale κ).pi1 v (scaleCoaches κ b) sel) -
              (I.scale κ).detCost v (scaleCoaches κ b)| ≤ C * Real.sqrt ((κ : ℕ) : ℝ)) := by sorry

end RailwayRM
