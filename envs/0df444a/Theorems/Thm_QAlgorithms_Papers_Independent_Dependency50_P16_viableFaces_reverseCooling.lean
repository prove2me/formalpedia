-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_viableFaces_reverseCooling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.viableFaces_reverseCooling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:29:51.00537+00:00
-- url     : https://prove2.me/theorems/7a6ce188-2bec-43dc-a496-464d36628bba
-- title:
--   Proposition 4.21: Viable faces and reverse cooling
-- statement:
--   For a GKSL generator on $\mathbb C^n$, consider all simplex faces other than vertices. Then
--
--   $$[\text{all such faces viable and not purely Hamiltonian}]\ \Longrightarrow\ [\text{reverse coolable}]\ \Longrightarrow\ [\text{all such faces viable}].$$
--
--   For a viable face, purely Hamiltonian means that every induced vector field tangent along the face vanishes on it. These are two implications, not an equivalence.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 21, Proposition 4.21: Viable faces and reverse cooling

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

/-- arXiv:2308.00561v1, PDF p.21, Proposition 4.21: Viable faces and reverse cooling. Footnote 16 is used verbatim in the face predicate: all tangent fields vanish. Full face is included among the nonvertex faces. -/
theorem viableFaces_reverseCooling {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (i0 : Fin n) (hi0 : i0.val = 0) :
    ((∀ F : Face n, 2 ≤ F.support.card → viable D (faceSet F) ∧ ¬purelyHamiltonianFace D F) →
      reverseCoolable D i0) ∧
    (reverseCoolable D i0 → ∀ F : Face n, 2 ≤ F.support.card → viable D (faceSet F)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
