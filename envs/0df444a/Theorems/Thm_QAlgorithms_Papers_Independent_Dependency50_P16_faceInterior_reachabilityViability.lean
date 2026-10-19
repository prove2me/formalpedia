-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_faceInterior_reachabilityViability
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.faceInterior_reachabilityViability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:22:45.649103+00:00
-- url     : https://prove2.me/theorems/57b1621d-17df-4955-bfb2-03324f32972c
-- title:
--   Lemma 4.4: Reachability of face interiors implies viability
-- statement:
--   Let $F$ be a nonvertex simplex face, let $\mu\in\operatorname{relint}F$, and let $\lambda\in\Delta^{n-1}$ satisfy $\lambda\ne\mu$. If
--
--   $$\mu\in\overline{\operatorname{reach}_C(\lambda)},$$
--
--   then $F$ is viable for (C). The starting point may itself lie in $F$.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 13, Lemma 4.4: Reachability of face interiors implies viability

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

/-- arXiv:2308.00561v1, PDF p.13, Lemma 4.4: Reachability of face interiors implies viability. Closure is retained. No extra hypothesis x outside F is added; only x != mu is required. -/
theorem faceInterior_reachabilityViability {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (hF : 2 ≤ F.support.card) (mu x : Vec n)
    (hmu : mu ∈ faceInterior F) (hx : x ∈ simplex n) (hne : x ≠ mu)
    (hreach : mu ∈ closure (reachC D x)) : viable D (faceSet F) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
