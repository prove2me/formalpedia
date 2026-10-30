-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact19
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:03:30.992662+00:00
-- url     : https://prove2.me/theorems/58b89c4f-78b5-4b02-9c12-aa6f80b55211
-- title:
--   Fact 19: coset expansion of a Young projector
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Use an orthonormal matrix realization $\varphi^\mu$ of the actual Specht space and the inclusion of $S_{N-1}$ fixing letter $N$. Define the unscaled subgroup Fourier operators $F_{ij}^\mu=\sum_{\pi\in S_{N-1}}\varphi^\mu_{ji}(\pi^{-1})V(\pi)$, with both indices in the full $\mu$ space. Then
--
--   $$P_\mu=\frac{d_\mu}{N!}\sum_{a=1}^{N}\sum_{i,j=1}^{d_\mu}\varphi^\mu_{ij}((a,N))V((a,N))F_{ij}^\mu.$$
--
--   This keeps the factorial prefactor of Eq.(63), even though the final line of its proof drops it.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 20, Fact 19: coset expansion of a Young projector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.20–21 Fact19: full mu indices even on subgroup inputs;
the Fourier sum is unscaled and the d_mu/N! prefactor is retained. -/
theorem fact19 (d k : ℕ) (hd : 2 ≤ d) (b : Schur.Partition d (k+2)) :
    Schur.isotypicProjector b = ((sdim b:ℂ) / ((k+2).factorial:ℂ)) •
      ∑ a : Fin (k+2), ∑ i : Fin (sdim b), ∑ j : Fin (sdim b),
        spechtMatrix b (Equiv.swap a (Fin.last (k+1))) i j •
          (Schur.tensorPermutation d (k+2) (Equiv.swap a (Fin.last (k+1))) *
          fourierSubgroup b i j) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
