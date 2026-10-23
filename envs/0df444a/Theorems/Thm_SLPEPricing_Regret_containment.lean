-- Prove2me | Theorems.Thm_SLPEPricing_Regret_containment
-- name    : SLPEPricing.Regret.containment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:17.506114+00:00
-- url     : https://prove2.me/theorems/6857ce26-1958-4acc-aea5-3445f770036e
-- title:
--   p. 17, opening of the proof of Theorem 1 — on the good event of earlier rounds, p* lies in every round's range [p^L_i, p^H_i]
-- statement:
--   Assume the standing hypotheses of Theorem 1. Fix an argmax selector, a pair selector, a noise realisation $\epsilon$, a horizon $T\ge2$ and a round $i\ge1$. If Assumption 2 and the concentration event $|\bar D_{n_j}(p^M_j)-d(p^M_j)|\le\Delta_j^2/\rho^2$ hold in every earlier round $j=1,\dots,i-1$, then the optimal price lies in round $i$'s price range:
--   $$p^L_i\le p^*\le p^H_i .$$
--
--   This is the round-by-round invariant of SLPE: the shrinking price ranges never lose the optimal price, so the policy's prices converge to $p^*$.
--
--   **Formalization Note** The page says "with high probability"; the statement is posed pathwise on the good event of the earlier rounds (for $i=1$ there is no hypothesis and the claim is $0\le p^*\le1$). Rounds are 1-based.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 17, paragraph after Theorem 1 (used on p. 22, Step 1 of the proof of Theorem 1)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- The containment claim (p. 17), pathwise. Under the standing hypotheses, for every argmax
selector, pair selector, noise realisation, `T ≥ 2` and round `i ≥ 1`: if Assumption 2 and the
concentration event hold in rounds `1, …, i - 1`, then `p^L_i ≤ p* ≤ p^H_i`. -/
theorem containment (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hamax : IsArgmaxSelector amax)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T) (i : ℕ) (hi : 1 ≤ i)
    (hgood : ∀ j ∈ Finset.Ico 1 i,
      Assumption2At μ ρ T sel ε j ∧ ConcentrationAt d μ ρ amax sel ε T j) :
    pL d μ ρ amax sel ε T i ≤ pstar ∧ pstar ≤ pH d μ ρ amax sel ε T i := by sorry

end SLPEPricing.Regret
