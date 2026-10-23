-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_zeroErrorGraphInvariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.zeroErrorGraphInvariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:49:30.443675+00:00
-- url     : https://prove2.me/theorems/3d128d9e-3555-4266-a9f4-ca1d86e5201b
-- title:
--   Unnumbered remark: zero-error NS∩PPT value depends only on the bipartite graph
-- statement:
--   Let $\mathcal N,\mathcal G:A\to B$ be CPTP channels on the same nonzero finite registers. Let $K(\mathcal N)$ denote the complex span of its Kraus operators as maps from $A$ to $B$, equivalently the span over all normalized Kraus presentations. If $K(\mathcal N)=K(\mathcal G)$, then
--
--   $$M_{0,\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N)=M_{0,\mathrm{NS}\cap\mathrm{PPT}}(\mathcal G).$$
--
--   This is invariance under the noncommutative bipartite graph. The space $K$ is distinct from the operator graph spanned by products $E_i^\dagger E_j$ used in the Lovasz bound.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 21, Unnumbered remark

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.21, unnumbered remark: dependence on the bipartite Kraus space K.
Typed space equality is a common choice of computational coordinates. -/
theorem zeroErrorGraphInvariance [Nonempty A] [Nonempty B] (N G : Superop A B)
    (hN : IsChannel N) (hG : IsChannel G) (hK : bipartiteGraph N = bipartiteGraph G) :
    zeroMessages true N = zeroMessages true G := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
