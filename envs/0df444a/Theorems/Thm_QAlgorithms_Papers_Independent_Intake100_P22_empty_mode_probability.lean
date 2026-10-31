-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_empty_mode_probability
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.empty_mode_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:36:42.934735+00:00
-- url     : https://prove2.me/theorems/adb6dc0a-bad4-4313-9797-f652d35c1701
-- title:
--   Empty-mode probability and its signed normalization
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Assume $n\ge1$. Let $\rho$ be a Gaussian density with real covariance $M$, and let $K$ have entries $K_{12}=1$, $K_{21}=-1$, all others zero. Define the Born probability $p_0=\operatorname{Tr}(\rho a_1a_1^\dagger)\in[0,1]$. For all such $M$, including singular matrices,
--   $$
--   p_0^2=\frac14\det(MK-I).
--   $$
--   On the additional domain $\det M\ne0$, its signed value is
--   $$
--   p_0=\frac12\operatorname{Pf}(M)\operatorname{Pf}(K-M^{-1}).
--   $$
--   The independent Born definition fixes the probability, without choosing an arbitrary square root. These formulas give outcome statistics for the first-mode measurement.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 5, §IV, Eqs.(20)–(21): empty-mode outcome probability

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4-5, Eqs.(20)-(21): empty-mode Born probability, its algebraic
square for every covariance, and its signed Pfaffian on the inverse domain. -/
theorem empty_mode_probability {n : ℕ} (hn : 0 < n) (s : CARSystem n)
    (rho : Op (Qubits n)) (M : Matrix (Major n) (Major n) ℝ) (h : StateWith s rho M) :
    let p := (rho * modeProjector s ⟨0, hn⟩ false).trace
    let Mc := M.map Complex.ofReal
    p.im = 0 ∧ (0 ≤ p.re ∧ p.re ≤ 1) ∧
      p ^ 2 = (1 / 4 : ℂ) * (Mc * firstK n - 1).det ∧
      (Mc.det ≠ 0 → p = (1 / 2 : ℂ) * pfaffian Mc * pfaffian (firstK n - Mc⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
