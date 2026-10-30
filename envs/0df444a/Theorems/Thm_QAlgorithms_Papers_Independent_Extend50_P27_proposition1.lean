-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition1
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:35:16.595924+00:00
-- url     : https://prove2.me/theorems/00b6be90-e749-4c06-96b8-a8221c98365f
-- title:
--   Proposition 1: reciprocity and a common one-box predecessor
-- statement:
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   For $N\ge1$, every $\alpha\vdash N-1$ and $
--   u\vdash N$ satisfy
--
--   $$
--   S^\alpha\subset\operatorname{Res}S^
--   u\iff S^
--   u\subset\operatorname{Ind}S^\alpha.
--   $$
--
--   For distinct $\mu,
--   u\vdash N$,
--
--   $$
--
--   u/\mu=\square\iff\exists\alpha\vdash N-1:\ S^\alpha\subset\operatorname{Res}S^
--   u\ \text{and}\ S^\mu\subset\operatorname{Ind}S^\alpha.
--   $$
--
--   The symbol $
--   u/\mu=\square$ means that one shape is obtained from the other by moving one box. Both equivalences connect representation occurrence with the Young graph.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 5, Proposition 1: reciprocity and a common one-box predecessor

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

/-- Proposition 1, both reciprocity and the common-predecessor equivalence
(PDF pp.5–6). Occurrence is actual intertwiner multiplicity. -/
theorem proposition1 {K : ℕ} :
    (∀ (alpha : Partition (K+1) K) (nu : Partition (K+1) (K+1)),
      (0 < restrictionMultiplicity alpha nu ↔ 0 < inductionMultiplicity nu alpha)) ∧
    (∀ (mu nu : Partition (K+1) (K+1)), mu ≠ nu →
      (BoxMove nu.val mu.val ↔ ∃ alpha : Partition (K+1) K,
        0 < restrictionMultiplicity alpha nu ∧ 0 < inductionMultiplicity mu alpha)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
