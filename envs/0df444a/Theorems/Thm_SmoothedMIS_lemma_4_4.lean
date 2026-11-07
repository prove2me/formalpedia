-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_4_4
-- name    : SmoothedMIS.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:51.47046+00:00
-- url     : https://prove2.me/theorems/c2ca76e0-989f-4a1d-8e07-a2cdf76bc90b
-- title:
--   Lemma 4.4 — $J$ is independent, and under condition (1) it dominates $\mathcal A$
-- statement:
--   Let $G$ be a base graph on $n$ vertices with distinct identifiers, $J_C$ any rule assigning an MIS to every identifier-labelled graph, and fix any outcome of the random edges and marks. Then the set $J$ computed in Step 2 (through $\mathrm{Gather}(\mathcal G,\mathcal A,\ell)$) is independent in $\mathcal G$, and if condition (1) holds then
--   $$
--   \mathcal A\subseteq N_{\mathcal G}[J].
--   $$
--
--   Together with Lemma 4.5 this is what makes $S\cup J$ dominate all high vertices in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: the fixed deterministic MIS rule of Step 2 (e.g. greedy by identifier) → every rule that maps each identifier-labelled graph to an MIS of it; reason: the lemma holds for each such rule, in particular the paper's
--   - generalization: the standing parameters β ≥ 1 and n of §4 → every real β and every n; reason: the lemma is deterministic and its proof uses no property of β or n
--   - encoding: the sets of Steps 1–2 under the random edges and the marks → functions of a fixed coin outcome ω = (ω_R, ω_κ) of the analysis model; reason: the statement is pointwise
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 4.4, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_SmoothedMIS_gatherJ

namespace SmoothedMIS

/-- **Lemma 4.4** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS*
(manuscript, sha256 dc2131db…), Lemma 4.4, p.20). The set `J` computed in Step 2 is independent
in `𝒢`. If condition (1) holds, then `𝒜 ⊆ N_𝒢[J]`.

**Formalization Note** Pointwise in the coins `ω = (ω_R, ω_κ)` of the centralized analysis model:
`𝒢 = addSmooth G ω_R`, `𝒜 = activeSet`, `J = gatherJ` (defined through the output of the
procedure `Gather(𝒢, 𝒜, ℓ)`), for every MIS-valued rule `J_C` and distinct identifiers. No
hypothesis on `β` or `n` is needed. -/
theorem lemma_4_4 (n : ℕ) (β : ℝ) (G : SimpleGraph (Fin n)) (ids : Fin n → ℕ)
    (hids : Function.Injective ids) (rule : LGraph → Set ℕ) (hrule : IsMISRule rule)
    (ω : Coins n) :
    (∀ u ∈ gatherJ β G ids rule ω, ∀ v ∈ gatherJ β G ids rule ω,
      ¬ (addSmooth G ω.1).Adj u v) ∧
    (cond1 β G ω → activeSet β G ω ⊆ closedNbhd (addSmooth G ω.1) (gatherJ β G ids rule ω)) := by sorry

end SmoothedMIS
