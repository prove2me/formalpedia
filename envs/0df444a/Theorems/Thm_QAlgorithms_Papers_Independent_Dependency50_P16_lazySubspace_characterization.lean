-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_lazySubspace_characterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.lazySubspace_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:40:33.484985+00:00
-- url     : https://prove2.me/theorems/f65945a5-08ba-43c3-9834-7d85f07eabbc
-- title:
--   Lemma C.8: Characterization of lazy subspaces
-- statement:
--   Let $G$ be represented by arbitrary CP data $(K,V_k)$ on $\mathbb C^n$, $n\ge2$, and let $S\ne0$ be a complex linear subspace with orthogonal projection $P$. The following are equivalent: every jump leaves $S$ invariant; the relaxation algebra leaves $S$ invariant;
--
--   $$P^\perp G(PAP)P^\perp=0\quad\text{for every }A;$$
--
--   the same zero block holds for some normalized density with support exactly $S$; and there exists, equivalently every, unitary $U$ whose first $\dim S$ columns span $S$ for which $(G_U)_{ij}=0$ whenever $j\le\dim S<i$. These characterize lazy subspaces. The CP generator need not be trace preserving.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 32, Lemma C.8: Characterization of lazy subspaces

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

/-- arXiv:2308.00561v1, PDF p.32, Lemma C.8: Characterization of lazy subspaces. Correction (trap 30): printed clause (v) uses columns of U* and is vacuous for a fixed nonadapted U. Its proof and (2.4) force columns of U and existence of an adapted unitary, equivalently all adapted unitaries. Both corrected versions are explicit. No stochastic assumption on general inducedCP is made. -/
theorem lazySubspace_characterization {n r : ℕ} (hn : 2 ≤ n) (K : Mat n) (V : Fin r → Mat n)
    (S : Submodule ℂ (Hilbert n)) (hS : S ≠ ⊥) :
    List.TFAE [invariant (Set.range V) S,
      invariant (relaxationAlgebra V : Set (Mat n)) S,
      (∀ A : Mat n, (1 - orthogonalProjector S) * cpGenerator K V (orthogonalProjector S * A * orthogonalProjector S) *
        (1 - orthogonalProjector S) = 0),
      (∃ rho : Mat n, QAlgorithms.IsDensityMatrix rho ∧ densitySupport rho = S ∧
        (1 - orthogonalProjector S) * cpGenerator K V rho * (1 - orthogonalProjector S) = 0),
      (∃ U : Mat n, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ adapted U S ∧
        ∀ i j : Fin n, j.val < Module.finrank ℂ S → Module.finrank ℂ S ≤ i.val →
          inducedCP K V U i j = 0),
      (∀ U : Mat n, U ∈ Matrix.unitaryGroup (Fin n) ℂ → adapted U S →
        ∀ i j : Fin n, j.val < Module.finrank ℂ S → Module.finrank ℂ S ≤ i.val →
          inducedCP K V U i j = 0)] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
