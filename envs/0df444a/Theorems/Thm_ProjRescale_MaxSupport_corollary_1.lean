-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_corollary_1
-- name    : ProjRescale.MaxSupport.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:41.820091+00:00
-- url     : https://prove2.me/theorems/032ed7ea-e9cb-4e1f-a9fd-27c2434f71b9
-- title:
--   Corollary 1, p. 7 — if 𝒥(L, σ) and 𝒥(L⊥, σ) return index sets covering {1, …, n}, they are J(L), J(L⊥) and the outputs are maximum support points
-- statement:
--   Let $L \subseteq \mathbb R^n$ be a linear subspace and $\sigma > 0$. Suppose Algorithm 1 on input $(L, \sigma)$ outputs $(x, J)$ and Algorithm 1 on input $(L^\perp, \sigma)$ outputs $(\hat x, \hat J)$, and that
--
--   $$J \cup \hat J = \{1,\dots,n\}.$$
--
--   Then $J = J(L)$, $\hat J = J(L^\perp)$, $x$ is a maximum support point of $L \cap \mathbb R^n_+$ and $\hat x$ is a maximum support point of $L^\perp \cap \mathbb R^n_+$ (a point of the cone whose support $\{j : x_j > 0\}$ is the maximum support index set).
--
--   This is the stopping test of Algorithm 2: the covering condition, which the algorithm can check, certifies maximum support without knowing $\sigma(L)$ or $\sigma(L^\perp)$.
--
--   **Formalization Note** "$(x,J) = \mathcal J(L,\sigma)$" is `A1Halts L σ x J r`: some execution of Algorithm 1 on $(L,\sigma)$, with any admissible behaviour of the basic procedure, halts with output $(x, J)$ after $r$ rescaling steps. Since the conclusion is drawn for every such pair of executions, it covers every implementation of the basic procedure.
--
--   Differences from the source:
--   - encoding: "$(x,J) = \mathcal J(L,\sigma)$, the output of Algorithm 1" → some execution of the transition relation `A1Step L σ` halts with output $(x, J)$, for any admissible basic-procedure answers; reason: the basic procedure is any procedure satisfying step 3, so every execution's output is an output of Algorithm 1.
--   - reading: the corollary assumes $\sigma > 0$, while $\mathcal J(L,\sigma)$ is introduced (p. 7) and Algorithm 1 is stated (p. 6) for $\sigma \in (0,1)$ → hypothesis $0 < \sigma$, with Algorithm 1's transition relation defined for every real $\sigma$; reason: the page is ambiguous between the two ranges and the Lean takes the corollary's own, wider hypothesis (never the weaker reading); for $\sigma \in (0,1)$ it is exactly the paper's statement.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, p. 7, Corollary 1 (notation 𝒥(L, σ) on p. 7)

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

/-- Corollary 1, p. 7. Let `σ > 0`. If `(x, J) = 𝒥(L, σ)` and `(x̂, Ĵ) = 𝒥(L⊥, σ)` satisfy
`J ∪ Ĵ = {1, …, n}`, then `J = J(L)`, `Ĵ = J(L⊥)`, and `x`, `x̂` are maximum support points of
`L ∩ ℝⁿ₊` and `L⊥ ∩ ℝⁿ₊`. -/
theorem corollary_1 {n : ℕ} (L : Submodule ℝ (E n)) (σ : ℝ) (hσ : 0 < σ)
    (x xh : E n) (J Jh : Finset (Fin n)) (r rh : ℕ)
    (hx : A1Halts L σ x J r) (hxh : A1Halts Lᗮ σ xh Jh rh) (hcov : J ∪ Jh = Finset.univ) :
    J = maxSupp L ∧ Jh = maxSupp Lᗮ ∧ IsMaxSupportPoint L x ∧ IsMaxSupportPoint Lᗮ xh := by sorry

end ProjRescale.MaxSupport
