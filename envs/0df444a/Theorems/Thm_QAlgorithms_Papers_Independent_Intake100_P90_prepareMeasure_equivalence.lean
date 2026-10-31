-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P90_prepareMeasure_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P90.prepareMeasure_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:08:59.153846+00:00
-- url     : https://prove2.me/theorems/8af72f87-861b-4d89-9628-edea353509c4
-- title:
--   Prepare-and-measure and entanglement-based realizations agree
-- statement:
--   Fix a public encoding choice for $n$ qubits. At position $i$, Alice has normalized signals $\phi_i^0,\phi_i^1$, and Bob uses the source decoder $B_i=s_i(|0\rangle\langle\widehat\phi_i^1|+|1\rangle\langle\widehat\phi_i^0|)$, where the hatted vectors are normalized orthogonal complements, $s_i>0$, and $B_i^\dagger B_i\le I$. Let Eve apply an arbitrary joint unitary to all signals and a normalized pure ancilla. Construct Alice's encoding filter from the signals, and use the same Eve unitary and decoder in the entanglement-based realization with the normalized $n$-pair $\Phi^+$ resource. For Alice word $a$ and Bob outcome $k$, let $v_{a,k}$ and $w_{a,k}$ be the respective unnormalized prepare-and-measure and entanglement-based Eve vectors. Then
--
--   $$w_{a,k}=2^{-n/2}v_{a,k},\qquad |w_{a,k}\rangle\langle w_{a,k}|=2^{-n}|v_{a,k}\rangle\langle v_{a,k}|.$$
--
--   Their traces give the same physical joint outcome probabilities when Alice's uniform preparation probability $2^{-n}$ is included. Wherever the branch mass is positive, the normalized conditional Eve density matrices agree. Thus the classical outcomes and all retained quantum information agree, including after any common positive-probability sifting condition. This is an operational equivalence with the fixed public choices, not just a transpose identity.
--
--   **Formalization Note** The source omits the factor $2^{-n/2}$ in its branch equation. Physical filter scaling is explicit and identical on both sides; the raw nonorthogonal-signal decoder need not itself be a contraction. Alice's physical encoding uses positive factors $a_i$ making $a_i A_i$ a contraction. Its success probability, evaluated before Bob's filtering, is $p_A=(\prod_i a_i)^2>0$. Dividing each physical entanglement-based output block by $p_A$ gives exactly $2^{-n}|v_{a,k}\rangle\langle v_{a,k}|$. This conditions on a realizable encoding-success event rather than treating an unscaled nonunitary filter as deterministic.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, PDF p. 2, Unnumbered prepare-and-measure / entanglement-based equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

/-- PDF pp.1--2, prepare-and-measure equivalence; corrected scalar in the
printed branch identity: the EB branch is 2^(-n/2) times the PM branch.
The complete cq blocks, probabilities, and positive-mass conditional Eve
states agree, with uniform Alice probability 2^(-n) on the PM side.
B is the physical contraction obtained by scaling the source's decoder. The unscaled B92
decoder need not be a contraction; physical scaling is necessary before
its squared amplitudes are interpreted as absolute probabilities.
Alice's encoding filter also has explicit positive physical scaling. Its
success mass is evaluated before Bob's filter, and conditioning on that
success gives exactly the uniform PM cq blocks. Everything uses the same
public encoding/sifting choice. -/
theorem prepareMeasure_equivalence {n : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (hphi : ∀ i b, IsState (phi i b))
    (hat : Fin n → Bool → EuclideanSpace ℂ Bool)
    (hhat : ∀ i b, IsState (hat i b) ∧ inner ℂ (phi i b) (hat i b) = 0)
    (s : Fin n → ℝ) (hs : ∀ i, 0 < s i)
    (hB : ∀ i, (1 - (sourceDecoder (hat i) (s i)).conjTranspose *
      sourceDecoder (hat i) (s i)).PosSemidef)
    (aScale : Fin n → ℝ) (haScale : ∀ i, 0 < aScale i)
    (hA : ∀ i, (1 - ((aScale i : ℂ) • localEncoding (phi i)).conjTranspose *
      ((aScale i : ℂ) • localEncoding (phi i))).PosSemidef)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ)
    (eta : EuclideanSpace ℂ E) (heta : IsState eta) :
    let B := fun i => sourceDecoder (hat i) (s i)
    encodingSuccessMass phi U eta aScale = (∏ i, aScale i) ^ 2 ∧
    0 < encodingSuccessMass phi U eta aScale ∧
    ∀ a k : Qubits n,
      ebBranch phi B U eta a k =
        (((Real.sqrt 2)⁻¹ : ℂ) ^ n) • pmBranch phi B U eta a k ∧
      pureDensity (ebBranch phi B U eta a k) =
        (((2 : ℝ) ^ n)⁻¹ : ℂ) • pureDensity (pmBranch phi B U eta a k) ∧
      (pureDensity (ebBranch phi B U eta a k)).trace.re =
        ((2 : ℝ) ^ n)⁻¹ * (pureDensity (pmBranch phi B U eta a k)).trace.re ∧
      ((encodingSuccessMass phi U eta aScale)⁻¹ : ℂ) •
        pureDensity (physicalEbBranch phi B U eta aScale a k) =
        (((2 : ℝ) ^ n)⁻¹ : ℂ) • pureDensity (pmBranch phi B U eta a k) ∧
      (0 < (pureDensity (pmBranch phi B U eta a k)).trace.re →
        sourceConditionalEve (ebBranch phi B U eta a k) =
          sourceConditionalEve (pmBranch phi B U eta a k) ∧
        sourceConditionalEve (physicalEbBranch phi B U eta aScale a k) =
          sourceConditionalEve (pmBranch phi B U eta a k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P90

end
