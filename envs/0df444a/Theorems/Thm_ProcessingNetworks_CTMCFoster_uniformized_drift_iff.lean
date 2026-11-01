-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_uniformized_drift_iff
-- name    : ProcessingNetworks.CTMCFoster.uniformized_drift_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:39.110584+00:00
-- url     : https://prove2.me/theorems/fa5a4406-b592-4e72-88d9-fe3d6301a9b2
-- title:
--   Proof of Theorem D.27, p.298 — the drift condition of the generator and of the uniformized chain
-- statement:
--   Let $\Lambda$ be a generator matrix on a countable set $\mathscr S$, let $\eta\ge\sup_i\lambda(i)$, let $P$ be the matrix (D.30), and let $b,c>0$, $C\subseteq\mathscr S$ and $V:\mathscr S\to\mathbb R_+$. For each state $i$, condition (D.36) at $i$, namely
--
--   $$
--   \sum_{j\ne i}\Lambda_{ij}V(j)-\lambda(i)V(i)\le -c+b\,1_C(i),
--   $$
--
--   holds if and only if
--
--   $$
--   PV(i)\le V(i)-\frac c\eta+\frac b\eta\,1_C(i),
--   $$
--
--   each series being convergent. So a Lyapunov function for the continuous-time chain is one for the uniformized chain, with the same set $C$ and constants $b/\eta$ and $c/\eta$.
--
--   Differences from the source:
--   - generalization: the equivalence for all $i\in\mathscr S$, inside the proof of Theorem D.27 → the equivalence at each single state $i$, with $C$ not assumed finite and no irreducibility; reason: the statement for all $i$ follows by quantifying, and the two omitted hypotheses play no part in the equivalence
--   - encoding: $\Lambda V(i)$ and $PV(i)$ as sums → `DriftConditionAt` and an explicit `Summable` clause; reason: a real `tsum` of a divergent series is $0$ in Lean; for $V\ge0$ divergence means the value $+\infty$, which fails the printed inequality
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), proof of Theorem D.27, p.298 (PDF 314)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_CTMCFoster_uniformizedPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_DriftConditionAt

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm

/-- For `η ≥ sup_i λ(i)` and `P` the matrix (D.30), condition (D.36) at the state `i` is equivalent
to `PV(i) ≤ V(i) - c/η + (b/η) 1_C(i)`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), proof of
Theorem D.27, p.298 (PDF 314).

**Formalization Note** As in `DriftConditionAt`, `PV(i) = ∑_j P(i, j) V(j)` is taken with its
convergence asserted, so that the junk value of a divergent `tsum` plays no role. -/
theorem uniformized_drift_iff {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) {η : ℝ} (hle : ∀ i, holdRate Λ i ≤ η)
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (C : Set S) (V : S → ℝ) (hV : ∀ i, 0 ≤ V i) (i : S) :
    DriftConditionAt Λ V b c C i ↔
      Summable (fun j => (uniformizedPMF hΛ hle i j).toReal * V j) ∧
        ∑' j, (uniformizedPMF hΛ hle i j).toReal * V j ≤
          V i - c / η + C.indicator (fun _ => b / η) i := by sorry

end ProcessingNetworks.CTMCFoster
