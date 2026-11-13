-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_loopContractible_iff_pathExtensionSplits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.loopContractible_iff_pathExtensionSplits
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:22:58.360457+00:00
-- url     : https://prove2.me/theorems/0f6fd0c6-127a-47b6-8b2c-e9b5ad778eff
-- title:
--   Remark 5.4
-- statement:
--   Let $G$ be a topological group and $PG$ its compact-open based path group. Write $\Omega G$ for the kernel of evaluation $\operatorname{ev}_1:PG\to G$. Then
--
--   $$G\text{ is loop contractible}\quad\Longleftrightarrow\quad\exists\text{ a continuous group homomorphism }s:G\to PG\text{ with }\operatorname{ev}_1\circ s=\operatorname{id}_G.$$
--
--   This is the continuous splitting meaning of the semidirect-product assertion. With the parameter running from the identity element to the identity map, the section is $s(g)(t)=\Phi(g,t)$, and a section gives the homotopy $\Phi(g,t)=s(g)(t)$. No commutativity of $G$ is required.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 20, Remark 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Remark 5.4, PDF p. 20: the based-path extension splits by a continuous
group-homomorphic section exactly when G is loop contractible. The section
homotopy is phi(g,t)=s(g)(t), and the section from phi is g↦(t↦phi(g,t)). -/
theorem loopContractible_iff_pathExtensionSplits
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    LoopContractible G ↔
      ∃ s : C(G, BasedPaths G),
        (∀ g, basedPathEndpoint (s g) = g) ∧
        (∀ g h, s (g * h) = basedPathMul (s g) (s h)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
