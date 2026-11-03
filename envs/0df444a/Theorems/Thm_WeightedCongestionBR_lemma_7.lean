-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_7
-- name    : WeightedCongestionBR.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:32.460887+00:00
-- url     : https://prove2.me/theorems/50c6edd9-f818-49b6-8a0a-85129d578250
-- title:
--   Lemma 7 — $p\ge(2\alpha+1)\alpha\,\mathrm{PoA}_d(\alpha+1/p)=(2\alpha+1)\alpha\,\Phi_{d,\alpha+1/p}^{d+1}$
-- statement:
--   For any positive integer $d$, with $\alpha=d+1$ from (6) and $p$ from (9),
--
--   $$
--   p\ge(2\alpha+1)\,\alpha\cdot\mathrm{PoA}_d\Big(\alpha+\frac1p\Big)=(2\alpha+1)\,\alpha\,\Phi_{d,\alpha+\frac1p}^{d+1}.
--   $$
--
--   This is the property of $p$ that drives the contradiction in the proof of the Key Property (Theorem 3).
--
--   Differences from the source:
--   - encoding: PoA_d(α + 1/p) = Φ_{d,α+1/p}^{d+1} → IsLUB of PoASet d (α + 1/p) at Φ_{d,α+1/p}^{d+1}; reason: PoA_d is the supremum of PoASet; IsLUB at a value says the supremum is that value
--   - encoding: PoA_d(ρ) = sup over games Γ of max over ρ-equilibria of C(s)/C(s*) → PoASet ranges over ratios with C(s*) > 0; reason: games with C(s*) = 0 have the undefined ratio 0/0; Theorem 2's games have C(s*) > 0, so the supremum is unchanged
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the ratio is undefined
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 7, p.13

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_PoASet
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Lemma 7** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.13). For any positive integer `d`, the parameter `p` of (9) satisfies
`p ≥ (2α + 1) α · PoA_d(α + 1/p) = (2α + 1) α Φ_{d,α+1/p}^{d+1}`.

**Formalization Note** The equality `PoA_d(α + 1/p) = Φ_{d,α+1/p}^{d+1}` is stated as `IsLUB` of
`PoASet d (α + 1/p)` at that value; the inequality is then stated for the value. -/
theorem lemma_7 (d : ℕ) (hd : 1 ≤ d) :
    IsLUB (PoASet d (alphaC d + 1 / pConst d)) (genGolden d (alphaC d + 1 / pConst d) ^ (d + 1)) ∧
      (2 * alphaC d + 1) * alphaC d * genGolden d (alphaC d + 1 / pConst d) ^ (d + 1) ≤
        pConst d := by sorry

end WeightedCongestionBR
