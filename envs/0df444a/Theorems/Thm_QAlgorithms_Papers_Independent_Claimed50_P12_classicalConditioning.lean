-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_classicalConditioning
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.classicalConditioning
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:40:27.246911+00:00
-- url     : https://prove2.me/theorems/a0de8d60-7817-45c2-be94-eed5cd822e2b
-- title:
--   Classical conditioning gives an exact relative entropy identity
-- statement:
--   Let $A,B,C$ be nonzero finite-dimensional complex Hilbert spaces. Fix an orthonormal basis $\{|b\rangle\}$ of $B$, a probability distribution $p_b$, and density operators $\rho_{AC,b}$. Define $\rho=\sum_b p_b\rho_{AC,b}\otimes|b\rangle\langle b|_B$, with tensor factors reordered as $ABC$. Let $T:B\to BC$ be any CPTP map satisfying $T(|b\rangle\langle b|)=|b\rangle\langle b|\otimes\rho_{C,b}$, where $\rho_{A,b},\rho_{C,b}$ are the conditional marginals. Then $\sigma=(\mathrm{id}_A\otimes T)(\rho_{AB})=\sum_b p_b\rho_{A,b}\otimes|b\rangle\langle b|\otimes\rho_{C,b}$ is a Markov chain, and
--
--   $$D(\rho\|\sigma)=I(A:C\mid B)_\rho,\qquad F(\rho,\sigma)\ge2^{-I(A:C\mid B)_\rho/2}.$$
--
--   Entropy and relative entropy are in bits and $F$ is root fidelity. This identifies classical conditioning with conditional independence of the reconstructed state.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 3, ClassicalConditioning

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Classical conditioning, Eq.11–14 (PDF p.3). Every channel satisfying Eq.12 gives
the explicit Eq.13 state; it is Markov and its relative entropy equals the CMI. -/
theorem classicalConditioning {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (basis : Matrix.unitaryGroup B ℂ) (p : B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (rhoAC : B → Op (A × C)) (hrho : ∀ b, IsDensityMatrix (rhoAC b))
    (T : Superop B (B × C)) (hT : IsChannel T)
    (hbasis : ∀ b,
      T (fun i j => (basis : Op B) i b * conj ((basis : Op B) j b)) =
        Matrix.kronecker (fun i j => (basis : Op B) i b * conj ((basis : Op B) j b))
          (traceLeft (rhoAC b))) :
    let rho := qcq (basis : Op B) p rhoAC
    let sigma := qcqRecovered (basis : Op B) p rhoAC
    idTensorSuperop T (marginalAB rho) = sigma ∧ Markov sigma ∧
      normalizedRelativeEntropyBits rho sigma = ((cmi rho : ℝ) : EReal) ∧
      (2 : ℝ) ^ (-cmi rho / 2) ≤ rootFidelity rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
