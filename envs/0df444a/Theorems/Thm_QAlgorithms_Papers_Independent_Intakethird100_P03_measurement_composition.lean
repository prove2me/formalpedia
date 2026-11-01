-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_measurement_composition
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.measurement_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:59:58.892702+00:00
-- url     : https://prove2.me/theorems/4879c59d-a3a2-41c1-b431-3a2f83d3fdda
-- title:
--   Lemma 8: composite probability, closure, commutation and independence
-- statement:
--   Fix an orthogonal family $\Omega$ with support $N$. A measurement acts on each subspace $V$ by the identity on the measured system and an ancillary unitary $U_V$, with a specified output subregister. For any normalized $|\xi\rangle\in N$,
--
--   $$
--   \Pr[y]=\sum_{V\in\Omega}P(\xi,V)P_{U,C}(V,y).
--   $$
--
--   Products of measurement operators remain measurement operators. Operators with disjoint ancillary registers commute, even though they share the measured system. For two such measurements,
--
--   $$
--   P_{U'U'',C'\cup C''}(V,(y',y''))=P_{U',C'}(V,y')P_{U'',C''}(V,y'').
--   $$
--
--   The independence is conditional on $V$, not unconditional independence for a superposition of eigenspaces.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 16, Lemma 8: composite probability, closure, commutation and independence

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF pp.16–17, Lemma 8, all clauses: mixture probabilities, closure under products,
commutation on disjoint ancillary registers, and independence conditional on the eigenspace.
The measured system I is shared. -/
theorem measurement_composition {I : Type*} [Fintype I] [DecidableEq I]
    (r d m e t : ℕ) (O : OrthogonalProjectorFamily I r)
    (V W : Fin r → Matrix (Qubits d) (Qubits d) ℂ)
    (Z : Fin r → Matrix (Qubits e) (Qubits e) ℂ)
    (C : Fin m ↪ Fin d) (D : Fin t ↪ Fin e)
    (hV : ∀ v, V v ∈ Matrix.unitaryGroup (Qubits d) ℂ)
    (hW : ∀ v, W v ∈ Matrix.unitaryGroup (Qubits d) ℂ)
    (hZ : ∀ v, Z v ∈ Matrix.unitaryGroup (Qubits e) ℂ) :
    (∀ (x : EuclideanSpace ℂ I), IsState x → act O.support x = x → ∀ y : Qubits m,
      probEvent (act (measurementMatrix O V) (tensorVec x (zeroKet d)))
        (fun z => z.2 ∘ C = y) =
      ∑ v, subspaceProbability (pureDensity x) (O.proj v) * eigenspaceOutcomeProbability V C v y) ∧
    measurementMatrix O V * measurementMatrix O W = measurementMatrix O (fun v => V v * W v) ∧
    (∀ v, V v * W v ∈ Matrix.unitaryGroup (Qubits d) ℂ) ∧
    firstMeasurement (K := Qubits e) O V * secondMeasurement (J := Qubits d) O Z =
      secondMeasurement (J := Qubits d) O Z * firstMeasurement (K := Qubits e) O V ∧
    (∀ (v : Fin r) (y : Qubits m) (z : Qubits t),
      probEvent (act (V v ⊗ₖ Z v) (tensorVec (zeroKet d) (zeroKet e)))
        (fun p => p.1 ∘ C = y ∧ p.2 ∘ D = z) =
        eigenspaceOutcomeProbability V C v y * eigenspaceOutcomeProbability Z D v z) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
