-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_2
-- name    : WeightedCongestionBR.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:46.098313+00:00
-- url     : https://prove2.me/theorems/976ec1b0-9de7-4432-baf7-efd71145ac7a
-- title:
--   Lemma 2 — the smoothness infimum equals $\Phi_{d,\rho}^{d+1}$
-- statement:
--   Let $\rho\ge1$ and let $d$ be a positive integer. Then
--
--   $$
--   B:=\inf_{\substack{\lambda\in\mathbb R\\ \mu\in(0,1/\rho)}}\Big\{\frac{\lambda\rho}{1-\mu\rho}\ \Big|\ \forall x,y,z\ge0,\ f\in\mathfrak P_d:\ y f(z+x+y)\le\lambda y f(z+y)+\mu x f(z+x)\Big\}=\Phi_{d,\rho}^{d+1},
--   $$
--
--   and the infimum is attained by a feasible pair $(\lambda,\mu)$.
--
--   This is the key step of the smoothness argument behind Lemma 1 and Theorem 1; the extra variable $z$ is what allows groups of deviating players.
--
--   Differences from the source:
--   - generalization: B = Φ_{d,ρ}^{d+1} (an infimum) → IsGLB at Φ_{d,ρ}^{d+1} and Φ_{d,ρ}^{d+1} belongs to the set; reason: the proof (p.26) exhibits a feasible pair with value Φ_{d,ρ}^{d+1} (μ = μ̂/ρ); attainment is what Lemma 1 needs in multiplicative form, and the statement specializes to the source's equality
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 2, p.7 (proof in Appendix A, pp.24–26)

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_smoothSet
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Lemma 2** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.7; proof in Appendix A, pp.24–26). For any `ρ ≥ 1` and positive integer `d`,
`B := inf { λρ/(1 − μρ) | λ ∈ ℝ, μ ∈ (0, 1/ρ), ∀ x, y, z ≥ 0, f ∈ 𝔓_d :
y f(z + x + y) ≤ λ y f(z + y) + μ x f(z + x) } = Φ_{d,ρ}^{d+1}`.

**Formalization Note** The infimum is `IsGLB`. The statement adds that it is attained (the pair
`μ = μ̂/ρ` of the proof, p.26), which Lemma 1 uses in multiplicative form. -/
theorem lemma_2 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    IsGLB (smoothSet d ρ) (genGolden d ρ ^ (d + 1)) ∧
      genGolden d ρ ^ (d + 1) ∈ smoothSet d ρ := by sorry

end WeightedCongestionBR
