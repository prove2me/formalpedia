-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_attainedFrontier
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.attainedFrontier
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:03:59.242964+00:00
-- url     : https://prove2.me/theorems/88a23729-acca-4a58-a376-489189ecefd1
-- title:
--   Attained optimal information–disturbance frontier
-- statement:
--   Let $d\ge2$, and equip $\mathrm{SU}(d)$ with normalized Haar measure. An admissible instrument is a Borel measurable positive semidefinite four-wire operator density $V\mapsto R_V$ with integrable entries, a deterministic two-comb as its integral, and integrable score kernels. Wire order is $(3,2,1,0)$; the unknown channel is inserted exactly once from wire 1 to wire 2. Let $F$ be the average channel entanglement fidelity and $G$ the average estimation fidelity for input $\rho=I_d/d$, as in Eqs.(19)–(20). Write $\mathcal I=d^2G-1$ and $\mathcal D=(1-F)/(1-2/d^2)$.
--
--   For every prescribed $i\in[0,1]$, there exist $x,y\in[0,1]$ and $z\in[0,i]$ such that
--
--   $$
--   d^2(z-i)^2=4z(1-i),\qquad x=\sqrt z,\quad y=\sqrt{1-i},\quad x^2+y^2+2xy/d=1.
--   $$
--
--   The density $R_V=|\chi_V\rangle\langle\chi_V|$, where
--
--   $$
--   |\chi_V\rangle=x|V\rangle\!\rangle_{30}|V^*\rangle\!\rangle_{21}+y|I_d\rangle\!\rangle_{32}|I_d\rangle\!\rangle_{10},
--   $$
--
--   is admissible and has $F=1-(d^2-2)x^2/d^2$, $G=(2-y^2)/d^2$, $\mathcal I=i$, and $\mathcal D=z$. Moreover, $z$ is the least attainable normalized disturbance among all admissible physical instruments with normalized information $i$.
--
--   This states both the lower branch of the frontier and its physical attainment, rather than only a polynomial equation for the curve.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 7, §IV C, Eqs.(30)–(34); abstract on PDF p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF p.7, Eqs.(30)–(34), and pp.1,6: attained lower frontier among all physical
one-use instruments. The lower branch D<=I is retained. Reference values 1/d^2 and
2/d^2 are not asserted to bound every deliberately poor instrument.
Printed p.7 maximum-information endpoint: y=1,x=0; changed to x=1,y=0,
as fixed by Eq.(32) and the immediately following paragraph. Independent moderation pending. -/
theorem attainedFrontier (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    ∀ i : ℝ, 0 ≤ i → i ≤ 1 → ∃ x y z : ℝ,
      NormalizedParameters d x y ∧ 0 ≤ z ∧ z ≤ i ∧
      (d : ℝ)^2 * (z-i)^2 = 4*z*(1-i) ∧
      x = Real.sqrt z ∧ y = Real.sqrt (1-i) ∧
      IsHaarCombInstrument H (by omega) (optimalDensity x y) ∧
      channelScore H (optimalDensity x y) = 1 - ((d : ℝ)^2-2)*x^2/(d : ℝ)^2 ∧
      gain H (optimalDensity x y) = (2-y^2)/(d : ℝ)^2 ∧
      normalizedInformation H (optimalDensity x y) = i ∧
      disturbance H (optimalDensity x y) = z ∧
      IsLeast (attainableDisturbances H (by omega) i) z := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
