-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionDecomposition
-- name    : QAlgorithms.Papers.Independent.Renew46.P12.reflectionDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:10:15.481618+00:00
-- url     : https://prove2.me/theorems/ec99a1d1-54ae-4e2d-9816-07d800329694
-- title:
--   Structure-preserving reflection decomposition
-- statement:
--   Let $n\ge0$ and let $U$ be a unitary on $n$ qubits, with computational-basis columns $u_j=U|j\rangle$. Define $R_v=I-2|v\rangle\langle v|$ and
--
--   $$
--   U'=|0\rangle\langle1|\otimes U+|1\rangle\langle0|\otimes U^\dagger,
--   \qquad w_j^\pm=\frac{|1\rangle|j\rangle\pm|0\rangle|u_j\rangle}{\sqrt2}.
--   $$
--
--   Then $U'$ is unitary, both families consist of unit vectors, and for every normalized $|\psi\rangle$,
--
--   $$
--   U'(|1\rangle|\psi\rangle)=|0\rangle U|\psi\rangle,
--   \qquad U'=\prod_j R_{w_j^-}.
--   $$
--
--   The product has exactly $2^n$ factors, ordered by the fixed most-significant-bit-first basis identification; the factor with the least index acts first. Moreover, if every entry of $U$ has the four-integer representation with common denominator $(\sqrt2)^\kappa$, every coordinate of each $w_j^\pm$ has that representation with denominator $(\sqrt2)^{\kappa+1}$.
--
--   This decomposition preserves the arithmetic structure needed for synthesis, while simulating U on a specified ancillary input sector.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, PDF p. 1, Lemma 1 (continues on PDF p.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- Lemma 1, PDF pp.1–2, including the ring-preservation observation after its proof.
The constructed dilation simulates U with |1> -> |0>, and is the product of precisely
the 2^n negative-eigenvector reflections, in the fixed `orderedProd` convention.
Both signs give normalized vectors; a common exponent kappa for U gives kappa+1
for these vectors. The purely algebraic statement also includes n=0. -/
theorem reflectionDecomposition (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    simulationDilation U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ ∧
    (∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
      act (simulationDilation U) (tensorVec (ket true) psi) = tensorVec (ket false) (act U psi)) ∧
    (∀ (j : Qubits n) (s : Bool), IsState (reflectionVector U j s)) ∧
    simulationDilation U = orderedProd (fun j : Fin (2 ^ n) =>
      householderReflection (reflectionVector U ((bitsEquivFin n).symm j) true)) ∧
    (∀ kappa : ℕ, (∀ i j, HasDenominator (Real.sqrt 2) kappa (U i j)) →
      ∀ (j : Qubits n) (s : Bool) (z : Bool × Qubits n),
        HasDenominator (Real.sqrt 2) (kappa + 1) (reflectionVector U j s z)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P12
