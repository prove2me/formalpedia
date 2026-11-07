-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_5_1
-- name    : TreeCoverLB.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:48.744335+00:00
-- url     : https://prove2.me/theorems/92dfbfe9-c9d3-4687-af6a-2c46202709f4
-- title:
--   Theorem 5.1: $\mathrm{ind}_{\mathbb Z_p}(|I_{p,k}|)\le (k-1)^2-1$
-- statement:
--   For every $k\ge 3$ and every prime $p\ge k-1$,
--   $$
--   \operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)\le (k-1)^2-1,
--   $$
--   i.e. there is a continuous $\mathbb Z_p$-equivariant map $|I_{p,k}|\to|E_{(k-1)^2-1}\mathbb Z_p|$.
--
--   With Theorem 4.3 this gives the exponent $1/(k-1)^2$ of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: ind_G(X) ≤ (k − 1)² − 1 → there is a continuous ℤ_p-equivariant map |I_{p,k}| → |E_{(k−1)²−1}ℤ_p|; reason: E_dG ⊆ E_{d'}G equivariantly for d ≤ d', so the two are equivalent
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap

open Classical

namespace TreeCoverLB

/-- **Theorem 5.1** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 5.1, p.18 (PDF p.20)): for every `k ≥ 3` and every prime
`p ≥ k − 1`, `ind_{ℤ_p}(|I_{p,k}|) ≤ (k − 1)² − 1`.

**Formalization Note** `ind_G(X) ≤ D` (Definition 4.2, an infimum over `d`) is stated as the existence
of a continuous `ℤ_p`-equivariant map `|I_{p,k}| → |E_Dℤ_p|` with `D = (k − 1)² − 1`; this is equivalent
because `E_dG ⊆ E_{d'}G` equivariantly for `d ≤ d'`, so the set in Definition 4.2 is upward closed. -/
theorem theorem_5_1 (k : ℕ) (hk : 3 ≤ k) (p : ℕ) [Fact p.Prime] (hp : k - 1 ≤ p) :
    ∃ ψ : ((Fin k → ZMod p) → ℝ) → (Fin ((k - 1) ^ 2 - 1 + 1) × ZMod p → ℝ),
      IsAgreementIndexMap p k ((k - 1) ^ 2 - 1) ψ := by sorry

end TreeCoverLB
