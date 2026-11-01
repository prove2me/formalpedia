-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_uniformized_stationary_iff
-- name    : ProcessingNetworks.CTMCFoster.uniformized_stationary_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:52.993282+00:00
-- url     : https://prove2.me/theorems/6a719a92-9638-4a12-ad48-e9ccacea407b
-- title:
--   §D.7, p.297 — stationary distributions of the uniformized chain and of the continuous-time chain coincide
-- statement:
--   Let $\Lambda$ be a generator matrix on a countable set $\mathscr S$, let $\eta\ge\sup_i\lambda(i)$, and let $P$ be the matrix (D.30). A probability distribution $\pi$ on $\mathscr S$ satisfies
--
--   $$
--   \pi P=\pi
--   $$
--
--   if and only if $\pi\Lambda=0$. So the discrete-time chain $Z$ with transition matrix $P$ and the continuous-time chain $X$ with generator $\Lambda$ have the same stationary distributions.
--
--   This transfers existence and uniqueness of a stationary distribution from $Z$ to $X$ in the proof of Theorem D.27.
--
--   Differences from the source:
--   - generalization: any stationary distribution of $Z$ is a stationary distribution of $X$ → an if-and-only-if; reason: the converse is what uniqueness for $X$ in Theorem D.27 uses, and the printed direction is the implication from left to right
--   - encoding: $\eta\ge\sup_i\lambda(i)$ → `∀ i, holdRate Λ i ≤ η`; reason: the same condition, with no separate finiteness clause since it provides a real bound
--   - encoding: $\pi$ stationary for $X$, i.e. $\pi\Lambda=0$ → `Stability.IsStationaryDistribution` of $G$ and $\lambda$; reason: the published predicate is $\pi\Lambda=0$ written out through $\Lambda_{xy}=\lambda(x)G_{xy}$
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D, §D.7, p.297 (PDF 313), with (D.30), p.296 (PDF 312)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_uniformizedPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_IsStationaryChain

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm

/-- For `η ≥ sup_i λ(i)`, a probability distribution is stationary for the discrete-time chain `Z`
with transition matrix (D.30) if and only if it is stationary for the continuous-time chain `X`.
The book's sentence is the direction from `Z` to `X`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D,
§D.7, p.297 (PDF 313).

**Formalization Note** The stationary property of `X` is the published
`Stability.IsStationaryDistribution` of the jump matrix and the exit rates. -/
theorem uniformized_stationary_iff {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) {η : ℝ} (hle : ∀ i, holdRate Λ i ≤ η) (π : PMF S) :
    IsStationaryChain (uniformizedPMF hΛ hle) π ↔
      Stability.IsStationaryDistribution (jumpPMF hΛ) (holdRate Λ) π := by sorry

end ProcessingNetworks.CTMCFoster
