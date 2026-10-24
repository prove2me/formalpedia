-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_coset_probabilities
-- name    : QAlgorithms.Papers.Independent.Support50.P40.coset_probabilities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:04:01.756692+00:00
-- url     : https://prove2.me/theorems/4cfb922b-e82c-4ed3-ba09-660621a618fa
-- title:
--   Coset masses identify syndromes and residual logical Paulis
-- statement:
--   Fix a normalized additive code encoding one qubit into $p\ge1$ physical qubits. Its phase-inclusive stabilizer is commuting, excludes $-I$, and has $p-1$ independent generators. Let $\bar S$ be its phase-free label set and $\bar S^\perp$ its commutation centralizer. Choose complete representatives $e_i$ of physical syndromes and $s_j$ of logical $j\in\{I,X,Y,Z\}$, with the identity representatives at the zero syndrome and logical identity. The logical representatives act as the named Paulis on the entire encoded operator algebra. Let $P_f$ be the independent depolarizing error law, with identity probability $f\in[0,1]$ and other-Pauli probability $(1-f)/3$.
--
--   Then $P_f(\bar S)$ is exactly the mass of errors acting as the identity channel on the whole code. For $j\ne I$, $P_f(s_j\bar S)$ is the mass of undetected errors acting as logical $j$; $P_f(\bar S^\perp)$ is the no-syndrome probability. For every syndrome and logical label,
--
--   $$
--   a_i=\Pr(i)=P_f(e_i\bar S^\perp),\qquad
--   b_{ij}=\Pr(i,j)=P_f(e_i s_j\bar S).
--   $$
--
--   For the normalized encoded Bell input these are the syndrome and generalized Bell measurement probabilities. After correcting with $e_i^{-1}$, the unnormalized logical branch on any logical operator $\rho$ is $\sum_j b_{ij}\,\sigma_j\rho\sigma_j^\dagger$. Logical $I,X,Y,Z$ correspond to $\Phi^+,\Psi^+,\Psi^-,\Phi^-$ as density operators.
--
--   These identifications retain zero-mass outcomes without conditional division and supply the probability law used in the concatenation rate.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 8, Section II bullets and Eqs. (18)-(19): coset probabilities and logical outcomes

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.7--8,13, five probability interpretations and Eqs.(18)--(19).
All logical actions are compared on the entire encoded operator algebra;
the recovered branch retains its mass even for zero-probability syndromes. -/
theorem coset_probabilities {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    weightPolynomial f (stabilizerLabels C.stabilizer) =
      errorEventMass f (fun e : ErrorLabel (m + 1) =>
        ∀ rho : Matrix Bool Bool ℂ,
          conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
            conjSuperop (innerEncoderMatrix C) rho) ∧
    (∀ j : Pauli, j ≠ .I →
      weightPolynomial f (labelCoset (T.logicalRep j) (stabilizerLabels C.stabilizer)) =
        errorEventMass f (fun e : ErrorLabel (m + 1) =>
          e ∈ centralizerLabels C.stabilizer ∧ ∀ rho : Matrix Bool Bool ℂ,
            conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
              conjSuperop (innerEncoderMatrix C) (conjSuperop j.mat rho))) ∧
    weightPolynomial f (centralizerLabels C.stabilizer) =
      effectProb (syndromeProjector C T (fun _ => false)) (outputQ C f) ∧
    (∀ i, syndromeMass C T f i =
      effectProb (syndromeProjector C T i) (outputQ C f)) ∧
    (∀ i j, jointMass C T f i j =
      effectProb (pureDensity (bellBasis C T i j)) (outputRQ C f)) ∧
    (∀ i (rho : Matrix Bool Bool ℂ), recoveredBranch C T f i rho =
      ∑ j : Pauli, (jointMass C T f i j : ℂ) • conjSuperop j.mat rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
