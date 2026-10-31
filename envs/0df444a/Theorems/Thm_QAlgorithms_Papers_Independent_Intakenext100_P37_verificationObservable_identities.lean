-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_verificationObservable_identities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.verificationObservable_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:28:13.747961+00:00
-- url     : https://prove2.me/theorems/b5b40922-ab99-4ae3-9c3e-be83f60095e1
-- title:
--   Unnumbered observable identities, Eqs.19–20
-- statement:
--   Let $\rho$ be a density matrix on key qubits $A,B$ and positive finite shields $A',B'$. For arbitrary shield unitaries $U_{ij}$, let $U_\tau=\sum_{ij}|ij\rangle\langle ij|\otimes U_{ij}$, let $\widetilde\rho=U_\tau\rho U_\tau^\dagger$, and let $\sigma=\operatorname{Tr}_{A'B'}\widetilde\rho$. For each of the five key observables $O=Z\otimes Z$, $R_1,R_2,I_1,I_2$, define $\widehat O=U_\tau^\dagger(O\otimes I)U_\tau$. Here $R_k$ is the difference of the real plus/minus Bell projectors in the even or odd key pair. For $I_k$ the first tilde Bell vector has relative phase $-i$ and the second has phase $+i$. Then
--
--   $$\operatorname{Tr}(\widehat O\rho)=\operatorname{Tr}((O\otimes I)\widetilde\rho)=\operatorname{Tr}(O\operatorname{Tr}_{A'B'}\widetilde\rho)=\operatorname{Tr}(O\sigma).$$
--
--   The parity observable is unchanged by conjugation. For the even ordered pair $(00,11)$ and the odd ordered pair $(01,10)$, these expectations are $2\operatorname{Re}\sigma_{uv}$ and $2\operatorname{Im}\sigma_{uv}$, respectively. Each of the four computational projectors is also unchanged by conjugation and its expectation equals the corresponding diagonal entry of $\sigma$. Thus the four joint outcomes of one local computational measurement setting recover all four diagonal entries; a single parity mean does not. The identities use genuine arbitrary controlled unitaries and do not depend on the faulty printed Eq. (21).
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 4, Unnumbered observable identities, Eqs.19–20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.4, Eqs.(19)--(20): all five conjugation/trace identities, both complex
coherences, and the FOUR joint outcomes of the local Z measurement setting.
The phase labels are fixed in imagCoherence so the imaginary sign is positive.
The parity mean alone is not asserted to determine four probabilities. -/
theorem verificationObservable_identities {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Key 2 × (Fin a × Fin b))) (hrho : IsDensityMatrix rho)
    (U : Key 2 → Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    physicalObservable U (Matrix.diagonal (fun k : Key 2 => if k.1 = k.2 then (1 : ℂ) else -1)) = Matrix.kronecker (Matrix.diagonal (fun k : Key 2 => if k.1 = k.2 then (1 : ℂ) else -1)) (1 : Op (Fin a × Fin b)) ∧
    (∀ i : Fin 5,
      (physicalObservable U (keyObservable i) * rho).trace =
        (Matrix.kronecker (keyObservable i) (1 : Op (Fin a × Fin b)) * twist U rho).trace ∧
      (Matrix.kronecker (keyObservable i) (1 : Op (Fin a × Fin b)) * twist U rho).trace =
        (keyObservable i * traceRight (twist U rho)).trace ∧
      (keyObservable i * traceRight (twist U rho)).trace =
        (keyObservable i * traceRight (twist U rho)).trace) ∧
    (∀ k : Key 2,
      physicalObservable U (Matrix.single k k 1) =
        Matrix.kronecker (Matrix.single k k 1) (1 : Op (Fin a × Fin b)) ∧
      (physicalObservable U (Matrix.single k k 1) * rho).trace = traceRight (twist U rho) k k) ∧
    (∀ odd : Bool,
      (physicalObservable U (realCoherence odd) * rho).trace.re =
        2 * (traceRight (twist U rho) (0, if odd then 1 else 0) (1, if odd then 0 else 1)).re ∧
      (physicalObservable U (imagCoherence odd) * rho).trace.re =
        2 * (traceRight (twist U rho) (0, if odd then 1 else 0) (1, if odd then 0 else 1)).im) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
