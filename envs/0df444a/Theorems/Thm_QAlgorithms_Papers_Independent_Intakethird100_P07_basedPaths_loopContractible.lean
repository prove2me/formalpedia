-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_basedPaths_loopContractible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.basedPaths_loopContractible
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:22:24.203603+00:00
-- url     : https://prove2.me/theorems/8cea7507-fad3-41a2-9317-f5676c352e6b
-- title:
--   Example 5.3
-- statement:
--   Let $G$ be any topological group, possibly noncommutative. Give its based path group $PG=\{\gamma\in C([0,1],G):\gamma(0)=e\}$ pointwise multiplication and the subspace topology of the compact-open mapping space. Then
--
--   $$\Phi(\gamma,s)(t)=\gamma(st)$$
--
--   is jointly continuous in $(\gamma,s)$, satisfies $\Phi(\gamma,0)=1_{PG}$ and $\Phi(\gamma,1)=\gamma$, and is a group endomorphism for each $s$. Thus the displayed homotopy makes $PG$ loop contractible.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 20, Example 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Example 5.3, PDF p. 20: the displayed rescaling is jointly continuous,
has the required endpoints, and is a path-group endomorphism at each time. -/
theorem basedPaths_loopContractible
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    Continuous (fun p : BasedPaths G × UnitTime => pathRescale p.1 p.2) ∧
    (∀ gamma : BasedPaths G, pathRescale gamma timeZero = basedPathOne) ∧
    (∀ gamma : BasedPaths G, pathRescale gamma timeOne = gamma) ∧
    (∀ (s : UnitTime) (gamma eta : BasedPaths G),
      pathRescale (basedPathMul gamma eta) s =
        basedPathMul (pathRescale gamma s) (pathRescale eta s)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
