-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_uniformized_irreducible
-- name    : ProcessingNetworks.CTMCFoster.uniformized_irreducible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:39.77372+00:00
-- url     : https://prove2.me/theorems/ffeb11af-4948-4d92-95f0-6f4550071dc1
-- title:
--   Proof of Theorem D.27, p.298 — the uniformized chain is irreducible
-- statement:
--   Let $\Lambda$ be a generator matrix on a countable set $\mathscr S$ whose continuous-time chain $X$ is irreducible, that is, whose jump matrix $G$ is irreducible. For every $\eta\ge\sup_i\lambda(i)$, the discrete-time chain $Z$ with transition matrix $P$ of (D.30) is irreducible.
--
--   This is the first step of the proof of Theorem D.27: it makes the discrete-time Foster–Lyapunov criterion applicable to $Z$.
--
--   Differences from the source:
--   - encoding: $Z$ irreducible → `KellyStochasticNetworks.MaxWeight.Irreducible`; reason: this is the hypothesis of the published discrete-time criterion, and it says that every state reaches every state with positive $n$-step probability
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), proof of Theorem D.27, p.298 (PDF 314)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_uniformizedPMF

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm

/-- If the continuous-time chain `X` is irreducible, so is the discrete-time chain `Z` with
transition matrix (D.30), for every `η ≥ sup_i λ(i)`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), proof of
Theorem D.27, p.298 (PDF 314).

**Formalization Note** The hypothesis is irreducibility of the jump chain (Definition D.10); the
conclusion is in the form of `KellyStochasticNetworks.MaxWeight.Irreducible`, the hypothesis of
the published Foster–Lyapunov criterion applied to `Z`. -/
theorem uniformized_irreducible {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) {η : ℝ} (hle : ∀ i, holdRate Λ i ≤ η)
    (hirr : Stability.Irreducible (jumpPMF hΛ)) :
    KellyStochasticNetworks.MaxWeight.Irreducible (uniformizedPMF hΛ hle) := by sorry

end ProcessingNetworks.CTMCFoster
