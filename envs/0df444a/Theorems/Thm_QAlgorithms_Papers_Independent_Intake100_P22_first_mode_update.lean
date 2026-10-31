-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_first_mode_update
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.first_mode_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:09:37.697211+00:00
-- url     : https://prove2.me/theorems/e7f21f7f-0ccc-46a6-93e7-35da3ef7153c
-- title:
--   Explicit empty-first-mode conditional update
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Assume $n\ge1$. Let $\rho$ be a Gaussian density with real covariance $M$ and $K_{12}=-K_{21}=1$, all other entries zero. Let $P_0=a_1a_1^\dagger$, $p_0=\operatorname{Tr}(\rho P_0)$, and suppose $p_0\ne0$. Then $p_0>0$, $\det(I-MK)\ne0$, and with $L=(I-MK)^{-1}M$,
--   $$
--   \omega(P_0\rho P_0,\theta)=\frac{p_0}{2^n}\exp\!\left(i\theta_1\theta_2+\frac i2\sum_{a,b=3}^{2n}L_{ab}\theta_a\theta_b\right).
--   $$
--   The output trace equals $p_0$, and $P_0\rho P_0/p_0$ is a Gaussian density. If $\det M\ne0$, also $p_0=\tfrac12\operatorname{Pf}(M)\operatorname{Pf}(K-M^{-1})$. No inverse of a singular $M$ is used for the update itself. This gives the conditional first-mode evolution, with an empty trailing block at $n=1$.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 11, §VIII: explicit conditional empty-first-mode update

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.11-12: explicit conditional empty-first-mode symbol. Nonzero outcome
probability implies the required inverse exists; invertibility of M is needed
only for the signed Pfaffian probability expression. -/
theorem first_mode_update {n : ℕ} (hn : 0 < n) (s : CARSystem n)
    (rho : Op (Qubits n)) (M : Matrix (Major n) (Major n) ℝ) (h : StateWith s rho M)
    (hprob : (rho * modeProjector s ⟨0, hn⟩ false).trace ≠ 0) :
    let p := (rho * modeProjector s ⟨0, hn⟩ false).trace
    let Mc := M.map Complex.ofReal
    let Y := conjSuperop (modeProjector s ⟨0, hn⟩ false) rho
    (1 - Mc * firstK n).det ≠ 0 ∧
      majoranaSymbol s Y = firstOutcomeSymbol p ((1 - Mc * firstK n)⁻¹ * Mc) ∧
      Y.trace = p ∧ 0 < p.re ∧ FermionicGaussianState s (normalizeComplexTrace Y) ∧
      (Mc.det ≠ 0 → p = (1 / 2 : ℂ) * pfaffian Mc * pfaffian (firstK n - Mc⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
