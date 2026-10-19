-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_orbitCovariance
-- name    : QAlgorithms.Papers.Independent.Information100.P10.orbitCovariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:37:02.660987+00:00
-- url     : https://prove2.me/theorems/d6dbeae0-997b-4945-b3ac-d5370d33119e
-- title:
--   Local-orbit Fubini–Study covariance and its trace, Eqs.(16)–(19)
-- statement:
--   Let $\psi$ be a normalized $M$-qubit pure state, and independently choose unit vectors $v_\mu\in\mathbb R^3$. Write $A_\mu=v_\mu\cdot\sigma^\mu$ for the local directional Pauli operator, $t_\mu=-iA_\mu\psi$, and $r_\mu=(\langle X_\mu\rangle,\langle Y_\mu\rangle,\langle Z_\mu\rangle)$. The Fubini–Study form is $h_\psi(a,b)=\langle a|b\rangle-\langle a|\psi\rangle\langle\psi|b\rangle$. Its pullback $g_{\mu\nu}=h_\psi(t_\mu,t_\nu)$ satisfies
--
--   $$g_{\mu\nu}=\langle\psi|A_\mu A_\nu\psi\rangle-\langle\psi|A_\mu\psi\rangle\langle\psi|A_\nu\psi\rangle,\qquad \operatorname{Re}\operatorname{tr}g=\sum_\mu[1-(v_\mu\cdot r_\mu)^2].$$
--
--   This identifies the geometric pullback with the local Pauli covariance, with the source's normalization.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 3, Local-orbit Fubini–Study covariance and its trace, Eqs.(16)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.3, Eqs.(16)-(19): the tangent pullback is Pauli covariance, with the printed trace. -/
theorem orbitCovariance {M : ℕ} (psi : Ket M) (hpsi : IsState psi)
    (v : Fin M → Direction) (hv : v ∈ directionDomain M) :
    (∀ q r, orbitMetric psi v q r =
      inner ℂ psi (act (directionalPauli q (v q) * directionalPauli r (v r)) psi) -
      inner ℂ psi (act (directionalPauli q (v q)) psi) *
        inner ℂ psi (act (directionalPauli r (v r)) psi)) ∧
    traceObjective psi v = ∑ q, (1 - (inner ℝ (v q) (bloch psi q)) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
