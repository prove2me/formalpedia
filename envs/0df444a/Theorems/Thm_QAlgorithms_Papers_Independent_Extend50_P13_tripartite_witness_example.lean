-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_tripartite_witness_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.tripartite_witness_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:48:10.414172+00:00
-- url     : https://prove2.me/theorems/fa0c9d50-2f9c-49b4-8f70-56a330eb8dc1
-- title:
--   Example 18 / Eq.(67): a tripartite witness inequality
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $P_-$ be the normalized three-factor antisymmetric projector and put $W=I/6-P_-$. For all complex $X,Y$,
--
--   $$f_W(X,Y)=\frac16[\operatorname{tr}(XY)I+\operatorname{tr}(X)Y+\operatorname{tr}(Y)X-XY-YX],$$
--
--   where $f_W$ is the ordinary two-input contraction of $W$. It is PSD for every PSD pair in any positive dimension, and $\operatorname{tr}(P_-\rho)\le1/6$ for every fully separable density matrix $\rho$. If $d\ge3$, $W$ is invariant and block positive, has negative expectation on an entangled density matrix, and vanishes on a separable density matrix. Its positive map saturates at a nonzero PSD pair; more specifically, for any nonzero orthogonal vectors $v,w$, $f_W(|v\rangle\langle v|,|w\rangle\langle w|)$ has a nonzero kernel vector. This uses the paper's saturation meaning of optimality.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 16, Example 18 / Eq.(67): a tripartite witness inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 18, Eqs.66–67 (PDF p.16). SOURCE CORRECTION: the printed polynomial
in Eq.67 is 6 f_W for W=I/6-P_(1,1,1), rather than f_W itself. Positivity holds in
all positive dimensions. Witness detection and saturation require d≥3. -/
theorem tripartite_witness_example
    (lambda : QAlgorithms.Schur.Partition 3 3) (hshape : lambda.val.rowLens = [1,1,1]) :
    (∀ (d : ℕ), 0 < d →
      let W : (Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) := (1/6 : ℂ) • 1-centralProjector d lambda
      (∀ X Y : (Matrix (Fin d) (Fin d) ℂ), contractInputs W ![X,Y] = (1/6 : ℂ) • witnessThree X Y) ∧
      (∀ X Y : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → Y.PosSemidef →
        (contractInputs W ![X,Y]).PosSemidef) ∧
      (∀ rho, QAlgorithms.IsDensityMatrix rho → FullySeparableDensity rho →
        (Matrix.trace (centralProjector d lambda * rho)).re ≤ 1/6)) ∧
    (∀ (d : ℕ), 3 ≤ d →
      let W : (Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) := (1/6 : ℂ) • 1-centralProjector d lambda
      OptimalWernerWitness W ∧ Saturates (contractInputs W) ∧
      ∀ v w : Fin d → ℂ, v ≠ 0 → w ≠ 0 → (∑ i, conj (v i)*w i) = 0 →
        ∃ z : Fin d → ℂ, z ≠ 0 ∧
          (contractInputs W ![rankOneOperator v v,rankOneOperator w w]).mulVec z = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
