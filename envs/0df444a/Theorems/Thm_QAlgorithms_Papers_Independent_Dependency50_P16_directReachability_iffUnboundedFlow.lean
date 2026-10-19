-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_directReachability_iffUnboundedFlow
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.directReachability_iffUnboundedFlow
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:05.443193+00:00
-- url     : https://prove2.me/theorems/9867dfea-f36e-4483-a25c-96835fd97203
-- title:
--   Proposition 4.12: Direct face reachability equals unbounded flow ratio
-- statement:
--   Let $F$ be a proper nonempty face of $\Delta^{n-1}$ with $d$ supported coordinates, $1\le d<n$. Then
--
--   $$\sup_{U\in SU(n)}R_d(U)=+\infty\quad\Longleftrightarrow\quad\exists\lambda\text{ solving (C)}:\ \lambda(0)\notin F,\ \lim_{t\to\infty}\lambda(t)\in\operatorname{relint}F.$$
--
--   Only $0/0$ is omitted from the flow-ratio domain; positive inflow divided by zero outflow is infinite. The initial state and limiting face point are existential.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 19, Proposition 4.12: Direct face reachability equals unbounded flow ratio

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

/-- arXiv:2308.00561v1, PDF p.19, Proposition 4.12: Direct face reachability equals unbounded flow ratio. The nonempty Face structure supplies d >= 1; the proper-face binder supplies d < n. No prescribed limiting point is asserted. -/
theorem directReachability_iffUnboundedFlow {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (hproper : F.support.card < n) :
    flowSup D.jump F.support.card = ⊤ ↔ directlyReachable D F := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
