-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_wick_correlators
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.wick_correlators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:34:41.528695+00:00
-- url     : https://prove2.me/theorems/e61edb75-33a0-41ac-a777-cfa8c51b3c65
-- title:
--   Wick Pfaffian formula from the Gaussian symbol
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $\rho$ be a Gaussian density with real skew covariance $M$, defined by $\omega(\rho,\theta)=2^{-n}e^{(i/2)\theta^TM\theta}$. For $p\ge0$ and strictly increasing indices $1\le a_1<\cdots<a_{2p}\le2n$, let $M|_a$ be the indicated principal submatrix. Then
--   $$
--   \operatorname{Tr}(\rho\,i^p c_{a_1}\cdots c_{a_{2p}})=\operatorname{Pf}(M|_a).
--   $$
--   The empty product and empty Pfaffian are both one. This determines higher even correlators from the two-point covariance.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 4, §IV, Eq.(17): Wick formula for Gaussian-state correlators

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eq.(17): Wick's Pfaffian formula follows from the Grassmann
Gaussian definition. Printed c_(2p) is corrected to c_(a_(2p)), as fixed by the
index list immediately after the display. The empty correlator is included. -/
theorem wick_correlators {n : ℕ} (s : CARSystem n) (rho : Op (Qubits n))
    (M : Matrix (Major n) (Major n) ℝ) (h : StateWith s rho M)
    (p : ℕ) (a : Fin (2 * p) → Major n) (ha : StrictMono a) :
    (rho * ((Complex.I ^ p) • monomial s (List.ofFn a))).trace =
      pfaffian (fun i j => (M (a i) (a j) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
