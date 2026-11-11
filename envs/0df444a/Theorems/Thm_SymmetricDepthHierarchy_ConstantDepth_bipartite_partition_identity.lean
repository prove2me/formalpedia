-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_bipartite_partition_identity
-- name    : SymmetricDepthHierarchy.ConstantDepth.bipartite_partition_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:48.728728+00:00
-- url     : https://prove2.me/theorems/9084b24c-ce44-4d2a-adb8-57307afe1696
-- title:
--   Lemma B.21, equation (7): $\mathrm{hom}_{\mathrm{bip}}(F,B(H))=\sum_{\mathcal R\in\Gamma(F)}\mathrm{hom}(F/\mathcal R,H)$
-- statement:
--   For every simple bipartite graph $F$ with fixed bipartition and every finite simple graph $H$,
--   $$\mathrm{hom}_{\mathrm{bip}}(F,B(H))=\sum_{\mathcal R\in\Gamma(F)}\mathrm{hom}(F/\mathcal R,H),$$
--   where $\Gamma(F)$ is the set of partitions of $V(F)$ into parts inducing connected subgraphs.
--
--   The identity transfers the separation of Lemma B.20 from arbitrary graphs to bipartite graphs with fixed bipartitions.
--
--   Differences from the source:
--   - encoding: B(H) with sides V(H) × {0} and V(H) × {1} → BipGraph with both sides V(H); (u,0) ~ (v,1) iff u = v or uv ∈ E(H); reason: the second coordinate only records the side
--   - encoding: partitions R of V(F) → Finpartition of the finite set of all vertices of F (parts nonempty); reason: Mathlib's finite partitions; parts of a partition are nonempty
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 37 (PDF p. 40), Lemma B.21, equation (7)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma B.21, equation (7), printed p. 37 (PDF p. 40). For every simple bipartite graph `F` with
fixed bipartition and every simple graph `H`,
`hom_bip(F, B(H)) = ∑_{R ∈ Γ(F)} hom(F/R, H)`. -/
theorem bipartite_partition_identity (F : BipGraph) {X : Type} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) :
    BipGraph.hombip F (BipGraph.lift H) =
      ∑ P ∈ connectedPartitions F.graph, homCount (quotientGraph F.graph P) H := by sorry

end SymmetricDepthHierarchy.ConstantDepth
