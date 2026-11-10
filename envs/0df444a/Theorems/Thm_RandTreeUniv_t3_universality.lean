-- Prove2me | Theorems.Thm_RandTreeUniv_t3_universality
-- name    : RandTreeUniv.t3_universality
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:33.52925+00:00
-- url     : https://prove2.me/theorems/f91cd646-e48a-4c8d-948a-a36ba6a413ac
-- title:
--   §6.3 — $G(n,C\ln n/n)$ is whp $\mathcal T_3$-universal
-- statement:
--   Let $K$ be a large absolute constant, $\alpha=n\ln\ln n/(K^3\ln n)$, and $\mathcal T_3$ the family of trees on $n$ vertices with maximum degree at most $\Delta$ that have no $K\alpha$ vertex-disjoint bare paths of length $n/(K^2\alpha)$ and more than $e^{\Delta^5}\alpha$ leaves. For a suitably large absolute constant $C>1$ and every $\Delta\ge2$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\big(G(n,C\ln n/n)\text{ is }\mathcal T_3\text{-universal}\big)=1 .
--   $$
--
--   This is the last case of the proof of Theorem 1 (§6.3); the paper presents its proof as a sketch.
--
--   Differences from the source:
--   - reading: a large absolute constant K (§4) and a suitably large absolute constant C → ∃ K₀, ∀ K ≥ K₀, ∃ C > 1, ∀ ∆ ≥ 2; reason: C does not depend on ∆; 'large enough' read as a threshold statement
--   - encoding: of size Kα, length n/(K²α) (T₁ membership) → ⌈Kα⌉ paths of length ⌈n/(K²α)⌉; reason: the paper ignores rounding; equivalent to 'at least' since sub-paths of bare paths are bare
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: isomorphic copy as a subgraph → SimpleGraph.IsContained (injective edge-preserving map, not necessarily induced); reason: same notion
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6.3, pp.51–52 (PDF 52–53) (unnumbered; concludes the proof of Theorem 1)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_InT3
import Definitions.Def_RandTreeUniv_IsUniversal

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **`T₃`-universality** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6.3, pp.51–52 (PDF 52–53), unnumbered; it concludes the proof of
Theorem 1): typically all trees in `T₃` can be simultaneously embedded in `G ∼ G(n, C ln n/n)` for
a suitably large absolute constant `C`. Here `T₃` consists of the trees on `n` vertices with
maximum degree at most `∆` that are not in `T₁` and have more than `exp(∆⁵)α` leaves.

**Formalization Note** Quantifiers: there is `K₀` such that for every `K ≥ K₀` there is an
absolute `C > 1` (before `∆`) such that for every `∆ ≥ 2`, `whp` ("with probability tending to 1 as `n → ∞`", footnote 2, p.1) `G(n, C ln n/n)` is
`T₃`-universal, with `α = n ln ln n/(K³ ln n)`. `G(n, p)` is the published `erProb`. -/
theorem t3_universality :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∃ C : ℝ, 1 < C ∧ ∀ Δ : ℕ, 2 ≤ Δ →
      Filter.Tendsto
        (fun n : ℕ => erProb n (C * Real.log n / n) (fun G => IsUniversal G (InT3 n K Δ)))
        Filter.atTop (nhds 1) := by sorry

end RandTreeUniv
