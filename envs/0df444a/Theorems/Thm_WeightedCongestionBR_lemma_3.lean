-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_3
-- name    : WeightedCongestionBR.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:36.827849+00:00
-- url     : https://prove2.me/theorems/851d46fb-d6d2-4dee-b262-966852b8c255
-- title:
--   Lemma 3 — $\Phi_{d,\rho}\le d/\mathcal W(d/\rho)$
-- statement:
--   For any $\rho\ge1$ and any positive integer $d$,
--
--   $$
--   \Phi_{d,\rho}\le\frac{d}{\mathcal W(d/\rho)},
--   $$
--
--   where $\mathcal W$ is the Lambert-W function. It gives the closed-form bound of Theorem 1 and the estimate $\Phi_{d,d+2}\le 4d$ behind the constant $p$.
--
--   Differences from the source: none.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 3, p.9

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_DirectTradeCoffee_lambertW
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Lemma 3** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.9). For any `ρ ≥ 1` and any positive integer `d`,
`Φ_{d,ρ} ≤ d / W(d/ρ)`, where `W` is the Lambert-W function. -/
theorem lemma_3 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    genGolden d ρ ≤ (d : ℝ) / DirectTradeCoffee.lambertW ((d : ℝ) / ρ) := by sorry

end WeightedCongestionBR
