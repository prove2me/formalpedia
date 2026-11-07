-- Prove2me | Theorems.Thm_ReplicableOL_lemma_4_2
-- name    : ReplicableOL.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:59.767177+00:00
-- url     : https://prove2.me/theorems/d3d4881e-60af-4f66-ab89-adb7f5baacf9
-- title:
--   Lemma 4.2 — phantom triangle inequality
-- statement:
--   For every $j$, almost surely,
--   $$
--   h^{14}_j\le2h_j,\qquad h^{23}_j\le2h_j,
--   $$
--   and the same holds conditionally on $\mathcal G_{j-1}\vee\sigma(\mu_j)$.
--
--   A phantom run compares an epoch rule with itself on two independent blocks, which is what the gain-weighted coin lemma needs; this inequality pays for that device with a factor 2, the price of adaptivity.
--
--   **Formalization Note** The statement is for all prefixes $h=S_{<j}$, $h'=S'_{<j}$ and, in the conditional form, for each mean $\mu\in[-1/4,1/4]$.
--
--   Differences from the source:
--   - generalization: almost surely, at $h=S_{<j}$, $h'=S'_{<j}$ → pointwise for all prefixes $h,h'$, and for every $\mu\in[-1/4,1/4]$ in the conditional form; reason: pointwise implies the a.s. statement through the identities of Lemma 4.1, at $\mu=\mu_j$
--   - generalization: the epoch rules of a learner satisfying (H2) at a fixed seed (Section 4 standing assumption, p.14) → an arbitrary `EpochRule k L`, which may read its whole current block; reason: p.17: "Within-epoch causality is not used: $\Phi_j(h;\cdot)$ may be any function of the block"; a learner's rule `𝓛.toEpochRule L r` is a special case
--   - generalization: Section 4 standing assumptions (p.14): $T=kL$, $\Delta\sqrt L\ge\sqrt3/8$ → no regime hypothesis and no condition on $L$; reason: the proof (pp.15–16, 35) uses neither; the statement specializes to the page under them
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 4.2, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Block
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_hazardAt
import Definitions.Def_ReplicableOL_hazard
import Definitions.Def_ReplicableOL_selfHazard
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 4.2.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 4.2, p.15. Both inequalities, unconditionally and given the mean `μ`.

**Formalization Note.** Stated pointwise in the prefixes `h`, `h'` (the a.s. statement at `h = S_{<j}`, `h' = S′_{<j}` is a special case). The conditional form is the same inequality for `hazardAt` at each `μ ∈ [−1/4, 1/4]`. -/
theorem lemma_4_2 {k L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (Φ : EpochRule k L) (j : Fin k)
    (h h' : Fin j → Block L) :
    selfHazard Δ Φ j h ≤ 2 * hazard Δ Φ j h h' ∧
    selfHazard Δ Φ j h' ≤ 2 * hazard Δ Φ j h h' ∧
    ∀ μ ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4),
      hazardAt Φ j h h μ ≤ 2 * hazardAt Φ j h h' μ ∧
      hazardAt Φ j h' h' μ ≤ 2 * hazardAt Φ j h h' μ := by sorry

end ReplicableOL
