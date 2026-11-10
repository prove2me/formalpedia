-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_6_21
-- name    : RandTreeUniv.theorem_6_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:00.973119+00:00
-- url     : https://prove2.me/theorems/72b5123e-9a87-494d-b08b-a1de4ee2fff4
-- title:
--   Theorem 6.21 — $G(n,C\ln n/n)$ is whp $\mathcal T_2''$-universal
-- statement:
--   Let $K$, $\alpha$, $\Gamma=\Delta^3$ be as in §6 and $\mathcal T_2''=\mathcal T_2\setminus\mathcal T_2'$: the trees of $\mathcal T_2$ for which Algorithm 6.5 applied to $T_1$ and $T_2$ yields $\min\{i_1,i_2\}<\Gamma+1$. There is a constant $C>1$ such that, for every $\Delta\ge2$ and $p=C\ln n/n$, with high probability $G(n,p)$ is $\mathcal T_2''$-universal.
--
--   Together with the $\mathcal T_2'$ statement (same $\delta_1$) it covers $\mathcal T_2$; this is Case 2 of §6 (rollback, absorption and linking systems).
--
--   Differences from the source:
--   - reading: a large absolute constant K (§4), a suitably large absolute constant C, δ₁ = δ₁(∆) suitably small → ∃ K₀, ∀ K ≥ K₀, ∃ C > 1, ∀ ∆ ≥ 2, ∃ δ₀ > 0, ∀ δ₁ ∈ (0, δ₀]; reason: C does not depend on ∆ or δ₁; δ₁ is chosen after ∆; 'large/small enough' read as threshold statements
--   - generalization: the decomposition T₁, …, T₄ fixed by the paper for each tree → membership if some four-tree decomposition has the stated outcome; reason: the family contains the paper's family for every choice of decomposition, so universality for it implies the paper's statement
--   - reading: i₁, i₂ = Γ + 1 (resp. min{i₁, i₂} < Γ + 1); roots r₁,₂, r₂,₃ of T; set of size (10 + δ₁)α → steps 1, …, Γ all pass (resp. one fails); roots {r₁,₂} for T₁ and {r₁,₂, r₂,₃} for T₂, distances in the whole tree; size at least (10 + δ₁)α; reason: the algorithm returns Γ + 1 exactly when steps 1, …, Γ pass; T₁ has the single root r₁,₂; tree distances agree with subtree distances
--   - encoding: of size Kα, length n/(K²α) (T₁ membership) → ⌈Kα⌉ paths of length ⌈n/(K²α)⌉; reason: the paper ignores rounding; equivalent to 'at least' since sub-paths of bare paths are bare
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: isomorphic copy as a subgraph → SimpleGraph.IsContained (injective edge-preserving map, not necessarily induced); reason: same notion
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6.2, Theorem 6.21, p.44 (PDF 45)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_InT2DoublePrime
import Definitions.Def_RandTreeUniv_IsUniversal

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Theorem 6.21** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.44 (PDF 45)). There is a constant `C > 1` such that, for every
`∆ ≥ 2` and `p = p(n) := C ln n/n`, whp `G(n, p)` is `T″₂`-universal. Here `T″₂ = T₂ \ T′₂`
consists of the trees for which Algorithm 6.5 applied to `T₁` and `T₂` yields
`min{i₁, i₂} < Γ + 1` (p.44).

**Formalization Note** Quantifiers: there is `K₀` such that for every `K ≥ K₀` there is an absolute
`C > 1` (before `∆`) such that for every `∆ ≥ 2` there is `δ₀ > 0` with the claim for every
`δ₁ ∈ (0, δ₀]` (`δ₁ = δ₁(∆)` "suitably small", p.31). `whp` ("with probability tending to 1 as `n → ∞`", footnote 2, p.1) is `Tendsto … atTop (𝓝 1)`. The family
is built on a four-tree decomposition chosen by "some decomposition" (see the definition), with
`α = n ln ln n/(K³ ln n)`. `G(n, p)` is the published `erProb`. -/
theorem theorem_6_21 :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∃ C : ℝ, 1 < C ∧ ∀ Δ : ℕ, 2 ≤ Δ →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ ≤ δ₀ →
        Filter.Tendsto
          (fun n : ℕ => erProb n (C * Real.log n / n) (fun G => IsUniversal G (InT2DoublePrime n K Δ δ₁)))
          Filter.atTop (nhds 1) := by sorry

end RandTreeUniv
