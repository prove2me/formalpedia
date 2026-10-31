-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_diagram_centralizer_and_kernel
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.diagram_centralizer_and_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:37:21.7924+00:00
-- url     : https://prove2.me/theorems/c1799da2-3e0c-4b7d-92a5-44fe5b9695a3
-- title:
--   Theorem 3.6: centralizer images and exact kernels
-- statement:
--   Let $n\ge1$, let $m\ge0$ be the doubled level, and put $k=\lfloor m/2\rfloor$. Let $V=\mathbb C^n$ with its permutation basis. Let $\Phi_{m/2}$ be the linear extension of the diagram equality-constraint matrices on $V^{\otimes k}$; at odd $m$ the last physical top and bottom indices are fixed to the last basis vector. If $(x_d)$ is the coarsening orbit basis, then
--
--   $$\operatorname{im}\Phi_{m/2}=\operatorname{End}_{G_m}(V^{\otimes k}),\qquad
--   \ker\Phi_{m/2}=\operatorname{span}_{\mathbb C}\{x_d:\#\operatorname{blocks}(d)>n\},$$
--
--   where $G_m=S_n$ for even $m$, and $G_m$ is the subgroup fixing the last basis index, isomorphic to $S_{n-1}$, for odd $m$. This describes both the full centralizer image and the exact kernel. The half-level action is the restricted permutation action.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 19, Theorem 3.6: centralizer images and exact kernels

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Image centralizer and exact kernel in both parities, PDF pp.19--20, Theorem 3.6.
At odd doubled level `m` the group consists exactly of permutations fixing the last basis vector,
i.e. the restricted permutation action of `S_(n-1)`. Both conclusions are retained. -/
theorem diagram_centralizer_and_kernel (n m : ℕ) (hn : 0 < n)
    (b : Module.Basis (LevelDiagram m) ℂ (DiagramSpace m)) (_hb : IsOrbitBasis m b) :
    (∀ a : Matrix (TensorIndex n (m / 2)) (TensorIndex n (m / 2)) ℂ,
      a ∈ LinearMap.range (partitionDiagramAction (m := m) hn) ↔
      ∀ s : Equiv.Perm (Fin n),
        (m % 2 = 1 → s ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩) →
        a * simultaneousValuePermutation s = simultaneousValuePermutation s * a) ∧
    LinearMap.ker (partitionDiagramAction (m := m) hn) =
      Submodule.span ℂ {v | ∃ d : LevelDiagram m, n < blockNumber d ∧ v = b d} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
