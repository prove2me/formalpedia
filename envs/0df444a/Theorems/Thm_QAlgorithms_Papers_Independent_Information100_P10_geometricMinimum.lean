-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_geometricMinimum
-- name    : QAlgorithms.Papers.Independent.Information100.P10.geometricMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:36:22.148901+00:00
-- url     : https://prove2.me/theorems/b8714d85-5b1c-43a7-b798-be6020a02018
-- title:
--   Unnumbered main result: geometric minimum principle and closed ED formula, Eqs.(18)–(24)
-- statement:
--   Let $M\ge0$ and let $\psi$ be a normalized pure state of $M$ qubits. For each wire $\mu$, let $r_\mu=(\langle X_\mu\rangle,\langle Y_\mu\rangle,\langle Z_\mu\rangle)\in\mathbb R^3$. Independently choose unit directions $v_\mu\in\mathbb R^3$ and put $\sigma_{v_\mu}^\mu=v_\mu\cdot\sigma^\mu$. Let $g$ be the pullback of the projective Fubini–Study Hermitian form to the tangents $-i\sigma_{v_\mu}^\mu\psi$, and define $E(\psi)=\inf_v\operatorname{Re}\operatorname{tr}g(\psi,v)$. Then
--
--   $$E(\psi)=M-\sum_{\mu=0}^{M-1}\|r_\mu\|_2^2=\sum_\mu(1-\|r_\mu\|_2^2)=\min_v\sum_\mu\bigl(1-|\langle\psi|\sigma_{v_\mu}^\mu\psi\rangle|^2\bigr).$$
--
--   The direction domain is nonempty and compact; its trace objective is continuous and bounded below. The trace and distance objectives coincide on this domain, and both infima are attained. A direction family minimizes exactly when each nonzero $r_\mu$ is aligned or antialigned with $v_\mu$; if $r_\mu=0$, every unit direction at that wire is optimal. In particular, simultaneous positive alignment at all nonzero vectors attains the minimum. This gives an explicit formula for the geometrically defined obstruction.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 1, Unnumbered main result: geometric minimum principle and closed ED formula, Eqs.(18)–(24)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF pp.3-4, Eqs.(18)-(24): the geometric minimum is attained and equals the Bloch formula.
At zero Bloch vectors every unit direction is optimal; division by zero is avoided. -/
theorem geometricMinimum {M : ℕ} (psi : Ket M) (hpsi : IsState psi) :
    (directionDomain M).Nonempty ∧ IsCompact (directionDomain M) ∧
    ContinuousOn (traceObjective psi) (directionDomain M) ∧
    BddBelow (traceObjective psi '' directionDomain M) ∧
    entanglementDistance psi = (M : ℝ) - ∑ q, ‖bloch psi q‖ ^ 2 ∧
    entanglementDistance psi = ∑ q, localED psi q ∧
    entanglementDistance psi = sInf (distanceObjective psi '' directionDomain M) ∧
    (∀ v ∈ directionDomain M, traceObjective psi v = distanceObjective psi v) ∧
    (∃ v ∈ directionDomain M, traceObjective psi v = entanglementDistance psi ∧
      distanceObjective psi v = entanglementDistance psi ∧
      ∀ q, bloch psi q ≠ 0 → v q = (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q) ∧
    (∀ v ∈ directionDomain M,
      traceObjective psi v = entanglementDistance psi ↔
      ∀ q, bloch psi q = 0 ∨
        v q = (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q ∨
        v q = -( (‖bloch psi q‖⁻¹ : ℝ) • bloch psi q)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
