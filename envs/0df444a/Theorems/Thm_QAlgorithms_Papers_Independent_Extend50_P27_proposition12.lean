-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition12
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:42:02.103143+00:00
-- url     : https://prove2.me/theorems/4af5d2aa-61d7-4dd9-b5e1-fd8c8ad7e1e4
-- title:
--   Proposition 12: physical branching and row-sum bounds
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   For every physical shape $
--   u$ with height $h(
--   u)\le d$, its number $n_
--   u$ of predecessors satisfies $n_
--   u\le h(
--   u)$. For each predecessor $\alpha$, the number of physical constituents of $\operatorname{Ind}S^\alpha$, counted with multiplicity, is at most $h(
--   u)+1$ if $h(
--   u)<d$ and at most $d$ if $h(
--   u)=d$. Consequently
--
--   $$\sum_\mu(M_N^{(d)})_{
--   u\mu}\le d^2.$$
--
--   The sum retains diagonal multiplicities rather than counting only nonzero positions.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 12, Proposition 12: physical branching and row-sum bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Proposition 12, retaining the branching counts and row sums with diagonal
multiplicities, and counting only physical induced constituents (PDF p.12). -/
theorem proposition12 {d K : ℕ} (hd : 0 < d) (nu : Partition d (K+1)) :
    removableCount nu.val ≤ nu.val.colLen 0 ∧ nu.val.colLen 0 ≤ d ∧
    (∀ alpha : Partition d K, Predecessor alpha.val nu.val →
      ((nu.val.colLen 0 < d →
        (∑ mu : Partition d (K+1), inductionMultiplicity mu alpha) ≤ nu.val.colLen 0 + 1) ∧
       (nu.val.colLen 0 = d →
        (∑ mu : Partition d (K+1), inductionMultiplicity mu alpha) ≤ d))) ∧
    (∑ mu : Partition d (K+1), teleportMatrix d (K+1) nu mu) ≤ (d : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
