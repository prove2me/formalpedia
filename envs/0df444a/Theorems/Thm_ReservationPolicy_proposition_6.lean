-- Prove2me | Theorems.Thm_ReservationPolicy_proposition_6
-- name    : ReservationPolicy.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:45.682001+00:00
-- url     : https://prove2.me/theorems/8dfd3bf1-eced-4c7d-84b4-84eca8aa6df1
-- title:
--   Proposition 6 — $s_0$ eliminates inequality and exceeds the welfare-maximizing transfer (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions and let $\kappa<\kappa^*$. Then
--
--   1. the benchmark equilibrium in which type $x$ invests exists and is unique;
--   2. for every feasible transfer $s$, the equilibrium under the policy exists and is unique; write $\sigma(s)$ for it;
--   3. the transfer
--   $$
--   s_0=\frac{4k\alpha(1-z)(1-\alpha)(1-\phi^2)}{32k^2+\phi^2-4k\bigl(1+2\phi^2+\alpha(1-\phi^2)\bigr)}
--   $$
--   is feasible, satisfies $EI(\sigma(s_0))=0$, and $|EI(\sigma(s))|>0$ for every other feasible $s$;
--   4. there is a feasible transfer $s^*$ with $U(\sigma(s))<U(\sigma(s^*))$ for every other feasible $s$, and
--   $$
--   s_0>s^*.
--   $$
--   So the transfer that eliminates educational inequality is strictly larger than the one that maximizes overall student welfare, and a policymaker who maximizes welfare leaves inequality in place.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - reading: s₀ "minimized" educational inequality → s₀ is the unique feasible zero of EI, so it uniquely minimizes |EI|; reason: signed EI falls linearly in s past s₀; the proof "solv[es] EI = 0" and the text says it "eliminates" inequality (p.24)
--   - reading: the policy equilibrium is not qualified by investment → the investing branch of the policy game, (17); reason: §3 focuses on type x investing; for κ just below (45) a separate no-investment outcome can also meet the quotas, and the paper does not discuss it
--   - generalization: κ < κ̂ (the focus of §3) → κ < κ*; reason: κ̂ ≤ κ̂̂ < κ*, so κ < κ̂ is covered
--   - generalization: s₀ and s* are stated as minimizer and maximizer → uniqueness of s₀ and s*, and existence and uniqueness of both equilibria; reason: these make the comparison meaningful and are implied by the proofs of pp.35–41
--   - encoding: the transfer range is left to p.41 → Feasible, the two conditions of p.41 with s ≥ 0; reason: the page names them after Proposition 5's proof
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), Proposition 6, p.24, with pp.41

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestBenchmark
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_Feasible
import Definitions.Def_ReservationPolicy_welfare
import Definitions.Def_ReservationPolicy_EI
import Definitions.Def_ReservationPolicy_Params_kappaStar
import Definitions.Def_ReservationPolicy_Params_sZero

namespace ReservationPolicy

/-- **Proposition 6.** For `κ < κ*`: the investing benchmark equilibrium exists and is unique; every
feasible transfer `s` has a unique policy equilibrium `σ s`; the transfer `s₀` of (24) is feasible, gives
`EI = 0`, and is the only feasible transfer with `EI = 0`; overall welfare has a unique maximizer `s*`
over feasible transfers; and `s* < s₀`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), Proposition 6,
p.24 (PDF 24), with p.41.

**Formalization Note** `s*` is characterized as the maximizer of `U` over the feasible set of p.41, not
defined by (56). "Minimized" is read as minimizing `|EI|`: the signed `EI` keeps falling past `s₀`. -/
theorem proposition_6 (P : Params) (hP : P.Valid) (hκ : P.κ < P.kappaStar) :
    ∃ b : Benchmark, IsInvestBenchmark P b ∧ (∀ b', IsInvestBenchmark P b' → b' = b) ∧
      ∃ σ : ℝ → PolicyOutcome,
        (∀ s, Feasible P b s → IsPolicyEq P b s (σ s)) ∧
        (∀ s o, Feasible P b s → IsPolicyEq P b s o → o = σ s) ∧
        Feasible P b P.sZero ∧ EI P (σ P.sZero) = 0 ∧
        (∀ s, Feasible P b s → s ≠ P.sZero → 0 < |EI P (σ s)|) ∧
        ∃ sstar, Feasible P b sstar ∧
          (∀ s, Feasible P b s → s ≠ sstar → welfare P (σ s) < welfare P (σ sstar)) ∧
          sstar < P.sZero := by sorry

end ReservationPolicy
