-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_corollary6
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.corollary6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:20:38.042053+00:00
-- url     : https://prove2.me/theorems/8c7e7374-c4ad-4b37-8b75-8f2eb23ff487
-- title:
--   Corollary 6: exact parity-block special synthesis
-- statement:
--   Let $n\ge1$ and let $V$ be an $n$-qubit unitary. Write $Z_n=\sigma_z^{\otimes n}$ and let $V_0,V_1$ be its restrictions to the full even- and odd-Hamming-weight spaces. Suppose
--
--   $$
--   Z_nVZ_n=V,\qquad\det V_0=\det V_1=1.
--   $$
--
--   Then $V$ is an exact finite product of $S$ gates, the four two-qubit gates $I-2|ab\rangle\langle ab|$ from Eq.(19), and the rotations $e^{i\theta\sigma_x\otimes\sigma_x}$, $0\le\theta<2\pi$, on arbitrary site pairs. No global-phase freedom is introduced. For $n=1$, the hypotheses force $V=I$.
--
--   This is the parity-preserving specialization of the explicit synthesis method.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 9, Corollary 6: parity-preserving block-special synthesis

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.9 Corollary 6, with both Eqs.(22)-(23) expanded. Exact synthesis, with no
uncontrolled global phase. For n=1 both sector determinants force the identity. -/
theorem corollary6 (n : ℕ) (hn : 1 ≤ n) (V : Op (Words Bool n))
    (hV : V ∈ Matrix.unitaryGroup (Words Bool n) ℂ)
    (hparity : parityZ n * V * parityZ n = V)
    (hdet : ∀ b : Bool, parityDet V b = 1) :
    V ∈ finiteGateProducts (parityFamily n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
