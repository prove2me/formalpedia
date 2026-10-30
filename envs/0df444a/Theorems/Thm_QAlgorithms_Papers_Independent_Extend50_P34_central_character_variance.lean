-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_central_character_variance
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.central_character_variance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:16:33.061462+00:00
-- url     : https://prove2.me/theorems/e27467bd-aeff-4f78-95ea-8de4b8150599
-- title:
--   Lemma 5.13
-- statement:
--   There is an absolute $b>0$ such that for every partition $\mu$ of weight $k\ge2$ and every $r,n,\omega$ in the standing regime,
--
--   $$\operatorname{Var}_{\lambda\sim\mathrm{SW}_r^n}p_\mu^\sharp(\lambda)\le\exp(bk^2\log k)r^{2k-2}/\omega^4.$$
--
--   The partition $(1)$ is included and has variance zero. This controls fluctuations of individual central characters.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 53, Lemma 5.13

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.13, arXiv:1501.05028v1, PDF p.53. The constant is uniform in mu,r,n,omega. No positive-variance hypothesis excludes the deterministic weight-two case. -/
theorem central_character_variance
    : ∃ b : ℝ, 0 < b ∧ ∀ mu : YoungDiagram, 2 ≤ observableWeight mu →
      ∀ r n : ℕ, ∀ omega : ℝ, RankRegime r n omega →
        schurVariance (n := n) (unif r) (sharp mu) ≤
          Real.exp (b*(observableWeight mu : ℝ)^2*Real.log (observableWeight mu)) *
            (r : ℝ)^(2*observableWeight mu-2)/omega^4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
