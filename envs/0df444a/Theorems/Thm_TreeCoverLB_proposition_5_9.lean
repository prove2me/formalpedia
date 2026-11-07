-- Prove2me | Theorems.Thm_TreeCoverLB_proposition_5_9
-- name    : TreeCoverLB.proposition_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:28.171642+00:00
-- url     : https://prove2.me/theorems/c82471f9-b95b-407d-9c4a-e49f790a9ae1
-- title:
--   Proposition 5.9: all marginals $\le 1/(k-1)$ iff uniform on an affine-plane configuration
-- statement:
--   Let $k\ge 3$, let $p\ge k-1$ be prime, and let $\mu\in|I_{p,k}|$. Then
--   $$
--   M_i(\mu)\le\frac1{k-1}\quad(i\in[k])
--   $$
--   if and only if $\operatorname{supp}(\mu)$ is an affine-plane configuration and $\mu$ is uniform on its support.
--
--   Differences from the source:
--   - encoding: M_i(µ) = max_a µ_i(a) ≤ 1/(k − 1); µ uniform on its support → µ_i(a) ≤ 1/(k − 1) for every a; µ(x) = 1/|supp µ| for x ∈ supp µ; reason: equivalent formulations
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Proposition 5.9, p.21 (PDF p.23); standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_marginal
import Definitions.Def_TreeCoverLB_IsAffinePlaneConfig

open Classical

namespace TreeCoverLB

/-- **Proposition 5.9** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Proposition 5.9, p.21 (PDF p.23); §5 standing assumptions p.18): let
`k ≥ 3`, let `p ≥ k − 1` be prime, `G = ℤ_p` and `X = |I_{p,k}|`. A point `µ ∈ X` satisfies
`M_i(µ) ≤ 1/(k − 1)` for every `i ∈ [k]` if and only if `supp(µ)` is an affine-plane configuration and
`µ` is uniform on its support.

**Formalization Note** `M_i(µ) = max_a µ_i(a) ≤ 1/(k−1)` is written `∀ a, µ_i(a) ≤ 1/(k−1)`. "Uniform
on its support" is `µ(x) = 1/|supp µ|` for every `x ∈ supp µ`. -/
theorem proposition_5_9 (k : ℕ) (hk : 3 ≤ k) (p : ℕ) [Fact p.Prime] (hp : k - 1 ≤ p)
    (μ : (Fin k → ZMod p) → ℝ) (hμ : μ ∈ realization (agreementComplex p k)) :
    (∀ (i : Fin k) (a : ZMod p), marginal μ i a ≤ 1 / ((k : ℝ) - 1)) ↔
      IsAffinePlaneConfig (supp μ) ∧ ∀ x ∈ supp μ, μ x = 1 / ((supp μ).card : ℝ) := by sorry

end TreeCoverLB
