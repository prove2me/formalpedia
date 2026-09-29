-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization
-- name    : WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/95866e94-b613-5ea5-be52-1afda717453d
-- title:
--   Specialisations with rootless 3-division polynomial in a weighted family
-- statement:
--   Let $a,b\in\mathbb{Q}[X]$ satisfy $\deg a\le 20$ and $\deg b\le 30$ (as `natDegree` bounds), and assume the coefficients $a_{20}$ of $X^{20}$ in $a$ and $b_{30}$ of $X^{30}$ in $b$ satisfy $4a_{20}^{3}+27b_{30}^{2}\ne 0$. Let $\Psi_3$ denote Mathlib's third division polynomial of a Weierstrass curve; for the curve written in Lean as $\langle 0,0,0,a,b\rangle$ over $\mathbb{Q}[X]$, i.e. $y^{2}=x^{3}+a(t)x+b(t)$ with $a_1=a_2=a_3=0$, $a_4=a$, $a_6=b$, assume further that $\Psi_3$ has no root in the coefficient ring: for every $g\in\mathbb{Q}[X]$ the evaluation of this $\Psi_3\in(\mathbb{Q}[X])[X]$ at $g$ is nonzero. Finally let $M$ be a natural number with $M\ne 0$ and let $m_0$ be any natural number. The conclusion is that there exists a natural number $m$ with $m_0\le m$ such that the rational Weierstrass curve $\langle 0,0,0,a(Mm),b(Mm)\rangle$ over $\mathbb{Q}$, obtained by evaluating $a$ and $b$ at the rational number $M\cdot m$, has the property that no $x\in\mathbb{Q}$ is a root of its $\Psi_3$. Thus the specialisation parameter is restricted to nonnegative integer multiples of $M$ and may be taken arbitrarily large, and the assertion about the specialised curve concerns rational roots of its $3$-division polynomial only (no statement is made about Galois representations here).
--
--   This is a Hilbert-irreducibility (Dörge-type) specialisation statement for the $3$-division polynomial of the one-parameter family $y^{2}=x^{3}+a(t)x+b(t)$, with weights $\mathrm{wt}(t)=1$, $\mathrm{wt}(x)=10$, the degree bounds $\deg a\le 20$, $\deg b\le 30$ making $y^{2}=x^{3}+a_{20}x+b_{30}$ the member at infinity and $4a_{20}^{3}+27b_{30}^{2}\ne 0$ its nonsingularity. Unlike the textbook form, which would produce infinitely many or a density statement of good specialisations, the Lean statement asserts only that arbitrarily large parameters $m\ge m_0$ inside a fixed arithmetic progression $t\equiv 0 \pmod M$ work, and it speaks of rational roots of $\Psi_3$ rather than of irreducibility of $\bar\rho_{E,3}$. It is used in [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists), where a member of the Rubin–Silverberg family with prescribed $5$-torsion is selected at such a specialisation and the absence of rational roots of $\Psi_3$ is then converted into irreducibility of the mod-$3$ representation, supplying the auxiliary curve for the $3$–$5$ switch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization (a b : Polynomial ℚ) (ha : a.natDegree ≤ 20) (hb : b.natDegree ≤ 30) (hinf : 4 * a.coeff 20 ^ 3 + 27 * b.coeff 30 ^ 2 ≠ 0) (hroot : ∀ g : Polynomial ℚ, (⟨0, 0, 0, a, b⟩ : WeierstrassCurve (Polynomial ℚ)).Ψ₃.eval g ≠ 0) (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ, ¬ (⟨0, 0, 0, a.eval ((M : ℚ) * m), b.eval ((M : ℚ) * m)⟩ : WeierstrassCurve ℚ).Ψ₃.IsRoot x := by sorry
