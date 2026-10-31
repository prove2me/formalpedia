-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_u1ThreeGates
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.u1ThreeGates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:19:29.581986+00:00
-- url     : https://prove2.me/theorems/f0b9b5d9-3ff7-459e-850e-7aa0cac67321
-- title:
--   An explicit U(1) semi-universal synthesis family
-- statement:
--   On $n\ge2$ qubits, use excitation-number symmetry $u(z)=\operatorname{diag}(1,z)$ for $z\in U(1)$. Its invariant operators are the same as for the paper's projective z-rotation convention. Let $\mathcal F$ consist of $S$ on every site, all four two-site phase gates $I-2|ab\rangle\langle ab|$ with $a,b\in\{0,1\}$, and $e^{i\theta(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)}$ on any pair of sites, for $0\le\theta<2\pi$. Then
--
--   $$
--   \bigoplus_{w=0}^n SU(\mathcal H_w)\subseteq\langle\mathcal F\rangle_{\mathrm{finite}}
--   \subseteq\mathcal V^{U(1)}_{n,2},
--   $$
--
--   where $\mathcal H_w$ is the full Hamming-weight-$w$ sector. This is exact semi-universality by the stated explicit gate family.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 9, V example, unnumbered: explicit U(1) semi-universal gate family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.9: the S, four controlled-phase and XX+YY gate families are U(1) semi-universal.
The representation diag(1,z) has the same invariant operators as exp(i theta sigma_z/2),
after reversing the circle parameter and removing a scalar phase. -/
theorem u1ThreeGates (n : ℕ) (hn : 2 ≤ n) :
    blockSpecial (sameCharge excitationPhases n) ⊆ finiteGateProducts (excitationFamily n) ∧
    finiteGateProducts (excitationFamily n) ⊆ symmetricLocalGroup excitationPhases n 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
