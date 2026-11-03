-- Prove2me | Theorems.Thm_WeightedCongestionBR_theorem_1
-- name    : WeightedCongestionBR.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:22.876762+00:00
-- url     : https://prove2.me/theorems/3516aad2-7889-4bc5-b41c-1f1e69a95e85
-- title:
--   Theorem 1 — $\mathrm{PoA}_d(\rho)\le\Phi_{d,\rho}^{d+1}\le[d/\mathcal W(d/\rho)]^{d+1}$
-- statement:
--   Let $d$ be a positive integer and $\rho\ge1$. The Price of Anarchy of $\rho$-approximate equilibria in weighted polynomial congestion games of degree $d$ satisfies
--
--   $$
--   \mathrm{PoA}_d(\rho)\le\Phi_{d,\rho}^{d+1}\qquad\text{and in particular}\qquad\mathrm{PoA}_d(\rho)\le\Big[\frac{d}{\mathcal W(d/\rho)}\Big]^{d+1}.
--   $$
--
--   Together with Theorem 2 it identifies $\mathrm{PoA}_d(\rho)=\Phi_{d,\rho}^{d+1}$, which Lemma 7 uses at $\rho=\alpha+1/p$.
--
--   Differences from the source:
--   - encoding: PoA_d(ρ) = sup over games of max over ρ-equilibria of C(s)/C(s*) → every ratio C(s)/C(s*) with s a ρ-equilibrium and s* a social-cost minimizer, C(s*) > 0, is at most the bound; reason: an upper bound on a supremum is an upper bound on each element; games with C(s*) = 0 have the undefined ratio 0/0
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 1, p.7

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_DirectTradeCoffee_lambertW
import Definitions.Def_WeightedCongestionBR_PoASet
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Theorem 1** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.7). The Price of Anarchy of `ρ`-approximate equilibria in weighted
polynomial congestion games of degree `d` is at most `Φ_{d,ρ}^{d+1}`; in particular
`PoA_d(ρ) ≤ [d / W(d/ρ)]^{d+1}`.

**Formalization Note** `PoA_d(ρ) ≤ B` is stated as: every element of `PoASet d ρ` is at most `B`. -/
theorem theorem_1 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ∀ q ∈ PoASet d ρ, q ≤ genGolden d ρ ^ (d + 1) ∧
      q ≤ ((d : ℝ) / DirectTradeCoffee.lambertW ((d : ℝ) / ρ)) ^ (d + 1) := by sorry

end WeightedCongestionBR
