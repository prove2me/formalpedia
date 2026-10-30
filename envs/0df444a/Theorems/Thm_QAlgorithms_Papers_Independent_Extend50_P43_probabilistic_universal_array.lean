-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_probabilistic_universal_array
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.probabilistic_universal_array
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:00:34.132235+00:00
-- url     : https://prove2.me/theorems/cd73a260-e0b1-481c-ac39-df8214e11b8a
-- title:
--   Heralded exact universal processing with 2m program qubits
-- statement:
--   Fix $m\geq1$. Let $A$ be the $m$-qubit data register and split the $2m$ program qubits into $B,C$. For every unitary $U$ on $m$ qubits, supply the explicitly constructed normalized program
--
--   $$
--   P_U=(I_B\otimes U_C)\Phi_m,\qquad \Phi_m=2^{-m/2}\sum_{x\in\{0,1\}^m}|x\rangle_B|x\rangle_C.
--   $$
--
--   The fixed processor measures each ordered pair $(A_i,B_i)$ in the Bell basis. Write $K_o\psi$ for the unnormalized remaining $C$ vector obtained by contraction with the product Bell bra for outcome $o$, and set $p_o(\psi)=\|K_o\psi\|^2$. The outcomes form a complete measurement, so $\sum_o p_o(\psi)=1$ for every normalized full input $\psi$. For every normalized data vector $d$, the designated outcome $o_+$ in which all pairs give $\Phi^+$ satisfies
--
--   $$
--   K_{o_+}(d\otimes P_U)=2^{-m}Ud,\qquad p_{o_+}(d\otimes P_U)=2^{-2m},\qquad \frac{K_{o_+}(d\otimes P_U)}{\sqrt{p_{o_+}(d\otimes P_U)}}=Ud.
--   $$
--
--   Thus the measured flag certifies exact output for every $U,d$ with the same positive probability. Register $C$ is designated as the output, as the source permits; no assertion is made about accidental agreement on failure outcomes.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 3, Unnumbered main construction: heralded exact universal processor with 2m program qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF pp.2–3, Eq.(11) and the all-Phi-plus construction: one fixed complete
Bell measurement implements every U with its explicit normalized 2m-qubit
program. Success amplitude is exactly 2^(-m) U d, probability is 2^(-2m),
and conditional C output is exactly U d. C is the allowed output location.
No claim is made that failure labels cannot accidentally give the same ray. -/
theorem probabilistic_universal_array (m : ℕ) (hm : 1 ≤ m) :
    (∀ psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m)),
      IsState psi → ∑ o : Fin m → Fin 4, bellOutcomeProbability o psi = 1) ∧
    ∀ U : Matrix (Qubits m) (Qubits m) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits m) ℂ →
      IsState (program U) ∧
      ∀ d : EuclideanSpace ℂ (Qubits m), IsState d →
        contractBellOutcome (successOutcome m) (tensorVec d (program U)) =
            ((2 : ℂ) ^ m)⁻¹ • act U d ∧
        bellOutcomeProbability (successOutcome m) (tensorVec d (program U)) =
            ((2 : ℝ) ^ (2 * m))⁻¹ ∧
        normalizedBellOutput (successOutcome m) (tensorVec d (program U)) =
            act U d := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
