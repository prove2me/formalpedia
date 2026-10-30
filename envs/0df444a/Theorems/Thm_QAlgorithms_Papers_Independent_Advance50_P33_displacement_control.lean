-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_displacement_control
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.displacement_control
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:32:17.718822+00:00
-- url     : https://prove2.me/theorems/c4dab453-23c6-406c-87d8-ed9637efbfc4
-- title:
--   The first positive momentum shift attains the displacement-only optimum
-- statement:
--   Fix a positive real odd-cat amplitude $A>0$, $\hbar=1$, and ideal photon parity measurement. Let $|c_0(A)\rangle$ be the normalized odd cat and displace it by $-d$ in momentum. Write $C_{\rm disp}(A,d)$ for one half of its even-parity probability. For every real $d$, the displaced state is normalized and
--   $$
--   f_A(d):=\langle P\rangle=
--   \frac{e^{-d^2}\bigl(e^{-2A^2}-\cos(2\sqrt2Ad)\bigr)}{1-e^{-2A^2}},\qquad C_{\rm disp}(A,d)=\frac{1+f_A(d)}4.
--   $$
--   There is a smallest positive solution $d_*$ of
--   $$
--   d\cos(2\sqrt2Ad)+\sqrt2 A\sin(2\sqrt2Ad)=d e^{-2A^2},
--   $$
--   and $C_{\rm disp}(A,d)\le C_{\rm disp}(A,d_*)$ for every real $d$. In fact, every complex displacement $D(z)$ of this cat has opposite-parity half-success at most $C_{\rm disp}(A,d_*)$. Thus the momentum-axis shift attains the maximum over the full displacement family. This is not an optimization over all Gaussian attacks.
--
--   **Source correction.** Eq. (10) prints an unprimed $\alpha$ in the sine coefficient; it is replaced by the same cat amplitude $A=\alpha'$ that occurs in the cosine, sine argument, and exponential, as differentiation requires. The quoted decimal illustration is rounded and is not asserted as an exact equality.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 5, III.C, Eqs.(10)–(11): extremizing displacement within the displacement family

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5--6, Eqs.(10)--(11): maximum over ALL displacements, attained on the
displayed momentum axis, for an initially odd cat. Eq.(10)'s printed unprimed alpha in its sine
coefficient is corrected to alpha_prime (A); see stationaryDisplacement and
HARD.md. The illustrative decimals 0.496 and 0.443 are rounded, not equalities.
No maximum over all Gaussian proof operations is asserted. -/
theorem displacement_control (A : ℝ) (hA : 0 < A) :
    CoherentRealized ∧ DisplacementRealized ∧
    (∀ d : ℝ, ‖pShift (-d) (cat (A : ℂ) false)‖ = 1 ∧
      photonParityMean (pShift (-d) (cat (A : ℂ) false)) = oddParityFormula A d ∧
      displacementControl (A : ℂ) false d = (oddParityFormula A d + 1) / 4) ∧
    ∃ d : ℝ, 0 < d ∧ stationaryDisplacement A d ∧
      (∀ p : ℝ, 0 < p → stationaryDisplacement A p → d ≤ p) ∧
      (∀ p : ℝ, displacementControl (A : ℂ) false p ≤ displacementControl (A : ℂ) false d) ∧
      (∀ z : ℂ, arbitraryDisplacementControl (A : ℂ) false z ≤
        displacementControl (A : ℂ) false d) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
