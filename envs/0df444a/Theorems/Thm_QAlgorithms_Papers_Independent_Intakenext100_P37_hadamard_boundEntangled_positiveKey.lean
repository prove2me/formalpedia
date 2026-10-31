-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_hadamard_boundEntangled_positiveKey
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.hadamard_boundEntangled_positiveKey
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:19:36.235014+00:00
-- url     : https://prove2.me/theorems/cd375ce5-34ca-4e46-a3f1-9d854e4a6284
-- title:
--   Main result: explicit 4 ⊗ 4 PPT bound entanglement with positive one-way key rate (Eq.16)
-- statement:
--   Let $H=2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, and let $\rho_H$ be the state computed from $U=H$ by Eqs. (9)–(11). The key registers $A,B$ and shields $A',B'$ are qubits; Alice owns $AA'$ and Bob owns $BB'$. Then $\rho_H$ is a density matrix, is invariant under transposition of $BB'$, is nonseparable across $AA':BB'$, and has zero asymptotic LOCC Bell-pair yield. Moreover, with binary entropy $h$ in bits,
--
--   $$r_H=1-h\!\left(\frac{\sqrt2}{1+\sqrt2}\right)>0,\qquad K_D(\rho_H)\ge r_H.$$
--
--   Measuring $A,B$ in the computational basis and applying one sequence of forward public-discussion protocols achieves $r_H$ bits per independent input copy. This sequence is selected before any finite-dimensional purifying Eve; its evaluated public transcript is included in the secrecy criterion. Shields remain private and unused. The result supplies the explicit $4\otimes4$ resource, without claiming a universal lower bound on dimension or equating the rounded printed decimal to the exact rate.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 1, Main result: explicit 4 ⊗ 4 PPT bound entanglement with positive one-way key rate (Eq.16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF pp.1--3, abstract and Eq.(16): explicit 4 tensor 4 PPT bound
entanglement and its exact positive one-way yield. No universal minimal-dimension
claim is made, and the rounded printed decimal is not used as an exact equality. -/
theorem hadamard_boundEntangled_positiveKey :
    IsDensityMatrix rhoHadamard ∧ transposeBob rhoHadamard = rhoHadamard ∧
    ¬ Entanglement.IsSeparableDensity (partyCut rhoHadamard) ∧
    Gap48.P42.bipartiteDistillable (physicalFin rhoHadamard) = 0 ∧
    0 < hadamardRate ∧ HasMeasuredOneWayRate rhoHadamard hadamardRate ∧
    ENNReal.ofReal hadamardRate ≤ Gap48.P42.distillableKey (physicalFin rhoHadamard) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
