-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_Supplement_theorem_D3_refuted
-- name    : SpilloverDuopoly.Switchers.Supplement.theorem_D3_refuted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:42:42.326+00:00
-- url     : https://prove2.me/theorems/c86411bd-c64e-42d8-9fc9-8fd12a37f571
-- title:
--   Theorem D.3 (corrected: refutation), p. 55 (PDF 57) — zero discount rules out the printed positive-profit threshold
-- statement:
--   Theorem D.3 is false on its printed domain. Set $T=N=2$, $c=\delta=0$, and take independent normal valuations with common mean $\mu$ and standard deviation 1 ($\rho=0$). Before trial, both products have expected value $\mu$. Learning and all later profits have zero present-value weight. Even allowing every admissible tie rule, no finite mean threshold guarantees a symmetric equilibrium with strictly positive overall profit for both firms.
--
--   $$\neg\exists\underline\mu\in\mathbb R\;\forall\mu\ge\underline\mu\;\exists\text{ admissible tie rule and }p:\quad\operatorname{NE}(p,p)\land\forall i,\ \pi_i(p,p)>0.$$
--
--   **Formalization Note.** The Lean statement quantifies over every first-period record with $c=\delta=0$, $V=\mu$, $u_0=0$ and admissible tie shares. `zeroDiscountProfit G` is share times price. Normal valuations need no additional field in this reduced boundary game because their mean is the only information available before trial and all later payoffs receive weight zero. The refutation concerns the threshold and strictly positive profit together; it does not deny existence of zero-profit equilibria.
--
--   Differences from the source:
--   - correction: Positive-profit symmetric equilibrium above a finite mean threshold for T≥N≥2. → Refutation at δ=0, T=N=2, c=0 for every admissible tie rule and independent normal valuations.; reason: Both positive profits force p>0 and λ<1; an undercut to (λp+p)/2 raises profit. Uncovered prices earn zero and future profits have zero weight.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 55 (PDF 57), Theorem D.3; §2 p. 6 (PDF 8), δ ∈ [0,1]

import Mathlib
import Definitions.Def_ImbalPricing_IsPureNash
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_PricingGames

namespace SpilloverDuopoly.Switchers.Supplement

/-- Refutation of Theorem D.3 as printed (p. 55, PDF 57). Take `T = N = 2`,
`c = δ = 0`, and independent normal valuations with common mean `mu` and standard
deviation one (`ρ = 0`). Since only first-period profit has positive weight, the
symmetric price game is exactly `zeroDiscountProfit`. No finite mean threshold can
guarantee a symmetric equilibrium with strictly positive overall profit for both firms.
Every admissible tie rule is allowed, including unequal shares.
The normal law does not appear in this reduced game: before trial its mean is the only
consumer valuation, and learning and all second-period profits receive weight zero. -/
theorem theorem_D3_refuted :
    ¬ ∃ threshold : ℝ, ∀ mu : ℝ, threshold ≤ mu →
      ∃ G : FirstPeriod (Fin 2), G.Standing ∧ G.c = 0 ∧ G.delta = 0 ∧
        G.V = mu ∧ G.u0 = 0 ∧ ∃ p : ℝ,
          ImbalPricing.IsPureNash (fun _ : Fin 2 => Set.univ)
            (fun i q => zeroDiscountProfit G q i) (fun _ => p) ∧
          ∀ i : Fin 2, 0 < zeroDiscountProfit G (fun _ => p) i := by sorry

end SpilloverDuopoly.Switchers.Supplement
