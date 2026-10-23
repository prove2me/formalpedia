-- Prove2me | Theorems.Thm_SLPEPricing_Regret_lemma_4
-- name    : SLPEPricing.Regret.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:22.443501+00:00
-- url     : https://prove2.me/theorems/f5157694-d3a6-4b06-bb87-3395a645ec58
-- title:
--   Lemma 4, p. 17 — on Assumption 2 and the concentration event of rounds 1…i, |p* − p̃*_i| ≤ MΔ_i²
-- statement:
--   Assume the standing hypotheses of Theorem 1 (smooth non-increasing demand $d$, interior unique revenue maximiser $p^*$, Assumption 1 with $\kappa$, the derivative bound $K_1$, the gradient condition with $c$, and $M\le\mu<2$, $\rho>0$). Fix an argmax selector, a pair selector, a noise realisation $\epsilon$, a horizon $T\ge2$ and a round $i\ge1$. If in every round $j=1,\dots,i$ Assumption 2 holds and
--   $$\big|\bar D_{n_j}(p^M_j)-d(p^M_j)\big|\le\Delta_j^2/\rho^2,$$
--   then the estimated optimal price of round $i$ satisfies
--   $$|p^*-\tilde p^*_i|\le M\Delta_i^2,\qquad M=\frac1c\Big(\frac1{\rho^2}+\frac{K_1}6+\frac\kappa4\Big)+\frac{K_1}{12}+4\kappa .$$
--
--   This is the core estimate of the analysis: the optimum of the piecewise linear surrogate is within $O(\Delta_i^2)$ of the true optimal price, which lets the next round shrink its price range to width $2\mu\Delta_i^2$.
--
--   **Formalization Note** The page states the bound "with probability at least $1-1/T^2$". Here it is posed pathwise, on the realisations where Assumption 2 and the concentration event hold in rounds $1,\dots,i$; the probability of the concentration event is the separate Hoeffding milestone. Assumption 2 is a property of the realisation (equal noise on the selected pairs), not an almost-sure statement, since under i.i.d. continuous noise it would have probability zero. Rounds are 1-based and $T\ge2$ guarantees $n_j\ge1$.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 17, Lemma 4 (proof pp. 18–22)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- Lemma 4 (p. 17), pathwise. Under the standing hypotheses, for every argmax selector, pair
selector, noise realisation, `T ≥ 2` and round `i ≥ 1`: if Assumption 2 and the concentration
event hold in rounds `1, …, i`, then `|p* - p̃*_i| ≤ M Δ_i²` with
`M = (1/c)(1/ρ² + K₁/6 + κ/4) + K₁/12 + 4κ`. -/
theorem lemma_4 (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hamax : IsArgmaxSelector amax)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T) (i : ℕ) (hi : 1 ≤ i)
    (hgood : ∀ j ∈ Finset.Icc 1 i,
      Assumption2At μ ρ T sel ε j ∧ ConcentrationAt d μ ρ amax sel ε T j) :
    |pstar - ptilde d μ ρ amax sel ε T i| ≤ Mconst c ρ K₁ κ * Delta μ i ^ 2 := by sorry

end SLPEPricing.Regret
