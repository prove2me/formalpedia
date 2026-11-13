-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kVectorSpace_loopContractible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kVectorSpace_loopContractible
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:23:35.262213+00:00
-- url     : https://prove2.me/theorems/a301f86e-ae9a-4dd4-9fc2-75986d3c7e9c
-- title:
--   Example 6.1
-- statement:
--   Let $V$ be a real vector-space object in the category of compactly Hausdorff generated spaces. Addition and scalar multiplication are continuous on the corresponding k-products, and negation is continuous. The scalar homotopy
--
--   $$\Phi(v,t)=tv,\qquad t\in[0,1],$$
--
--   is continuous on $k(V\times[0,1])$, runs from zero to the identity, and is additive at each time. Consequently $V$ is loop contractible in kTop. This uses the k-product topology without assuming continuity on ordinary products.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 25, Example 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Example 6.1, PDF p. 25: the explicit scalar homotopy contracts a
real k-vector space. Its operations are assumed continuous on k-products;
no ordinary-product continuity or loop-contractibility hypothesis is imposed. -/
theorem kVectorSpace_loopContractible
    (V : Type u) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [UCompactlyGeneratedSpace.{u} V]
    (hadd : Continuous (fun p : KSpace (V × V) => p.1 + p.2))
    (hneg : Continuous (fun x : V => -x))
    (hsmul : Continuous (fun p : KSpace (ℝ × V) => p.1 • p.2)) :
    IsKAddLoopContraction (scalarHomotopy (V := V)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
