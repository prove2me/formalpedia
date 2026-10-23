-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_projectedBlock_generatorIdentity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.projectedBlock_generatorIdentity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:39:45.602862+00:00
-- url     : https://prove2.me/theorems/f741ee6f-139c-4ba4-af71-09219f835d0e
-- title:
--   Lemma C.7: Projected-block generator identity
-- statement:
--   For a general CP-generator representation $G(X)=\sum_kV_kXV_k^*-KX-XK^*$, orthogonal projections $O,P,Q,R$, and arbitrary $A\in M_n(\mathbb C)$,
--
--   $$O\,G(PAR)\,Q=\sum_k(OV_kP)A(QV_kR)^*-(OKP)A(RQ)-(OP)A(QKR)^*.$$
--
--   This is the projected-block expansion of the generator. Trace preservation is not required.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 32, Lemma C.7: Projected-block generator identity

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

/-- arXiv:2308.00561v1, PDF p.32, Lemma C.7: Projected-block generator identity. Correction (trap 30): PDF p.32 prints L on the left, while its right side expands G=-L from (C.1). The statement uses G=-L. Rendered p.32 checked; no alternative global sign convention is introduced. -/
theorem projectedBlock_generatorIdentity {n r : ℕ} (hn : 2 ≤ n) (K : Mat n) (V : Fin r → Mat n)
    (O P Q R A : Mat n) (hO : O.IsHermitian ∧ O * O = O)
    (hP : P.IsHermitian ∧ P * P = P) (hQ : Q.IsHermitian ∧ Q * Q = Q)
    (hR : R.IsHermitian ∧ R * R = R) :
    O * cpGenerator K V (P * A * R) * Q =
      (∑ k, (O * V k * P) * A * (Q * V k * R)ᴴ) -
        (O * K * P) * A * (R * Q) - (O * P) * A * (Q * K * R)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
