-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unitality_sixCriteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unitality_sixCriteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:31:07.259276+00:00
-- url     : https://prove2.me/theorems/fb997195-08fd-40f7-b60c-050cbee77eab
-- title:
--   Lemma 5.1: Six characterizations of unitality
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, these six criteria are equivalent: unitality; vanishing $\sum_k[V_k,V_k^*]$ for some, equivalently every, jump representation; $L_Ue=0$ for every $U\in SU(n)$; equality of row and column sums of every $J(U)$; and
--
--   $$\operatorname{derv}(e/n)=\{0\},\qquad\operatorname{reach}_C(\lambda)\subseteq\{\mu:\mu\prec\lambda\}\quad\text{for every }\lambda\in\Delta^{n-1}.$$
--
--   Here $e=(1,\ldots,1)$, and $\prec$ is ordinary majorization. This is the exact reachable-set containment, without replacing it by its closure.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 22, Lemma 5.1: Six characterizations of unitality

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

/-- arXiv:2308.00561v1, PDF p.22, Lemma 5.1: Six characterizations of unitality. The proof-only erroneous factor 1/2 in L(I) is not transcribed. Both some and every representation formulations are explicit. -/
theorem unitality_sixCriteria {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    List.TFAE [unital D,
      someRepresentation D (fun E => ∑ k, (E.jump k * (E.jump k)ᴴ - (E.jump k)ᴴ * E.jump k) = 0),
      everyRepresentation D (fun E => ∑ k, (E.jump k * (E.jump k)ᴴ - (E.jump k)ᴴ * E.jump k) = 0),
      (∀ U, specialUnitary U → populationGenerator D.jump U *ᵥ (fun _ => 1) = 0),
      (∀ U, specialUnitary U → ∀ i, ∑ j, rates D.jump U i j = ∑ j, rates D.jump U j i),
      derivatives D (barycenter n) = {0},
      (∀ x ∈ simplex n, reachC D x ⊆ {y | majorizedBy y x})] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
