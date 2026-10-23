-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_constant_fixed_dimension_zero
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.constant_fixed_dimension_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:24:57.785922+00:00
-- url     : https://prove2.me/theorems/5c682b4e-64a6-411f-b8c8-429e290371d3
-- title:
--   Proposition 47
-- statement:
--   Let $a<b$ and let $\psi:[a,b]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous. If some integer $k\ge0$ satisfies $\dim\ker(\psi(t)-I)=k$ for every $t\in[a,b]$, then
--
--   $$\mu_{\rm RS}(\psi)=0.$$
--
--   Here $\mu_{\rm RS}$ is the graph index relative to the diagonal in the doubled symplectic space. Neither endpoint is required to be the identity or nondegenerate. The cases $k=0$ and $k=2n$ are included. The formal interval representation uses the positive affine parametrization $a+(b-a)t$.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 48, Proposition 47

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 47, PDF p.48; no endpoint restriction and k=0,2n are allowed. -/
theorem constant_fixed_dimension_zero {n : ℕ} (p : ℝ → GroupedRealMatrix n)
    (a b : ℝ) (hab : a < b) (hp : ContinuousOn p (Set.Icc a b))
    (hs : ∀ t ∈ Set.Icc a b, IsSymplectic (p t)) (k : ℕ)
    (hk : ∀ t ∈ Set.Icc a b, Module.finrank ℝ (crossingSpace false (p t)) = k) :
    robbinSalamon (fun t => p (a+(b-a)*t)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
