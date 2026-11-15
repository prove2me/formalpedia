-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_6
-- name    : UniversalNonstochastic.Main.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:30:12.769535+00:00
-- url     : https://prove2.me/theorems/341d1da9-a69b-433a-bd95-2221ec3f967d
-- title:
--   Theorem 6 — $\mathbf m(N_{\alpha,\beta}\cap\{K>k\})=\Theta(\tau(\max(\alpha,k)))$
-- statement:
--   There is a constant $c>1$ such that for all $\alpha,k\in\mathbb N_0$ and all real $\beta\ge0$,
--   $$\mathbf m\bigl(N_{\alpha,\beta}\cap\{\omega\mid K(\omega)>k\}\bigr)\le c\,\tau(\max(\alpha,k)),$$
--   and, if moreover $\beta\le2^{2^\alpha}$,
--   $$\tau(\max(\alpha,k))/c\le\mathbf m\bigl(N_{\alpha,\beta}\cap\{\omega\mid K(\omega)>k\}\bigr).$$
--
--   This is (7): requiring $K(\omega)>k$ in addition to nonstochasticity replaces $\alpha$ by $\max(\alpha,k)$, with no condition on $k$. For $k=0$ it contains the goal, Theorem 1.
--
--   Differences from the source:
--   - generalization: the upper bound in (7) for β ≤ 2^(2^α) → the upper bound for every real β ≥ 0; reason: the source states right after (7) that only the lower bound uses the condition on β; restricted to β ≤ 2^(2^α) this is exactly (7)
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 6, eq. (7) and the sentence after it, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Stochasticity

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 6, p.7, eq. (7): there is `c > 1` such that for all `α, k ∈ ℕ₀` and all real
`β ≥ 0`, `m(N_{α,β} ∩ {ω | K(ω) > k}) ≤ c τ(max(α, k))`, and, when `β ≤ 2^{2^α}`, also
`τ(max(α, k))/c ≤ m(N_{α,β} ∩ {ω | K(ω) > k})` (only the lower bound uses the condition on
`β`, as stated after (7)). -/
theorem theorem_6 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 1 < c ∧ ∀ (α : ℕ) (β : ℝ) (k : ℕ), 0 ≤ β →
      mass m (nonstochastic U α β ∩ {ω | (k : ℕ∞) < Kobj U ω}) ≤
          c * tail m ((max α k : ℕ) : ℝ) ∧
        (β ≤ (2 : ℝ) ^ (2 ^ α) →
          tail m ((max α k : ℕ) : ℝ) / c ≤
            mass m (nonstochastic U α β ∩ {ω | (k : ℕ∞) < Kobj U ω})) := by sorry

end UniversalNonstochastic.Main.Supplement
