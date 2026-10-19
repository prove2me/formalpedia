-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_asymptoticLimit_stabilizable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.asymptoticLimit_stabilizable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:22:15.395131+00:00
-- url     : https://prove2.me/theorems/a2eedae9-5b88-418e-87e0-70638688c14a
-- title:
--   Lemma 4.3: Asymptotic limits are stabilizable
-- statement:
--   Let $\lambda:[0,\infty)\to\Delta^{n-1}$ solve the convexified system (C) of a GKSL generator, and let $\mu\in\Delta^{n-1}$. If $\lambda(t)\to\mu$, then
--
--   $$0\in\operatorname{conv}(\operatorname{derv}(\mu)),\qquad\mu\in\operatorname{stab}_R.$$
--
--   Every asymptotic limit is stabilizable; a single stationary induced field is not required.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 13, Lemma 4.3: Asymptotic limits are stabilizable

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

/-- arXiv:2308.00561v1, PDF p.13, Lemma 4.3: Asymptotic limits are stabilizable.  -/
theorem asymptoticLimit_stabilizable {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (path : ℝ → Vec n) (hpath : relaxedSolution D (Set.Ici 0) path)
    (mu : Vec n) (hmu : mu ∈ simplex n) (hlim : Tendsto path atTop (nhds mu)) :
    stabilizable D mu := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
