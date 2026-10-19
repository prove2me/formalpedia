-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_boundedFlow_higherDimensionalBarrier
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.boundedFlow_higherDimensionalBarrier
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:25:32.965383+00:00
-- url     : https://prove2.me/theorems/8b7018ca-4e0a-402a-8697-a02c5b559005
-- title:
--   Lemma 4.9: Higher-dimensional flow barrier
-- statement:
--   Let $1\le d<n$ and suppose the $d$-dimensional flow-ratio supremum $R$ is finite. Write $p_d(\lambda)=\sum_{i=1}^d\lambda_i$. If $\lambda\in\Delta^{n-1}$, $\varepsilon>0$, and $\lambda_i\ge\varepsilon p_d(\lambda)$ for $i\le d$, then
--
--   $$p_d(\lambda)\ge\frac R{R+\varepsilon}\quad\Longrightarrow\quad p_d(v)\le0\quad\text{for every }v\in\operatorname{derv}(\lambda).$$
--
--   Moreover, no solution to (C) beginning outside any $(d-1)$-face can converge to a point in that face's relative interior. This is the higher-dimensional population barrier.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 18, Lemma 4.9: Higher-dimensional flow barrier

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.18, Lemma 4.9: Higher-dimensional flow barrier. Finite ENNReal supremum is checked before toReal; eps > 0 prevents zero denominator even at R=0. The empty flow domain has supremum 0. -/
theorem boundedFlow_higherDimensionalBarrier {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d < n) (hfinite : flowSup D.jump d ≠ ⊤) :
    (∀ x ∈ simplex n, ∀ eps : ℝ, 0 < eps →
      (∀ i : Fin n, i.val < d → eps * partialPopulation d x ≤ x i) →
      (flowSup D.jump d).toReal / ((flowSup D.jump d).toReal + eps) ≤ partialPopulation d x →
      ∀ v ∈ derivatives D x, partialPopulation d v ≤ 0) ∧
    (∀ F : Face n, F.support.card = d → ∀ path mu,
      relaxedSolution D (Set.Ici 0) path → path 0 ∉ faceSet F → mu ∈ faceInterior F →
      ¬Tendsto path atTop (nhds mu)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
