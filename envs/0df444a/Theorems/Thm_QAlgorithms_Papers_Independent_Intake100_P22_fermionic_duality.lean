-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_fermionic_duality
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.fermionic_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:48:45.617601+00:00
-- url     : https://prove2.me/theorems/1f7f6a64-4453-47b0-a4fb-1d7dac5d6e77
-- title:
--   Fermionic dual injectivity, Gaussian symbol, and positivity
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For a complex-linear parity-preserving $E$, let
--   $$
--   \rho_I=2^{-2n}\prod_{a=1}^{2n}(I+ic_ac_{2n+a}),\qquad
--   \rho_E=(E\otimes_f\mathrm{Id})(\rho_I).
--   $$
--   The two halves use the fixed disjoint CAR embeddings of Eq.(48). For every other complex-linear parity-preserving $F$,
--   $$
--   \rho_E=\rho_F\Rightarrow E=F,\qquad
--   E\text{ completely positive}\Longleftrightarrow\rho_E\ge0.
--   $$
--   If $E$ has Gaussian action $S$ and prefactor $C$, its dual has the exact symbol
--   $$
--   \omega(\rho_E,\theta,\eta)=\frac{C}{2^{2n}}e^{S(\theta,\eta)}.
--   $$
--   The dual is an operator rather than an assumed normalized state. Injectivity includes every odd monomial. This specifies a full linear map through its fermionic generating function.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 10, §VII, Definition 6 and Eq.(49): dual-operator injectivity and Gaussian form

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, Definition 6 and Eq.(49): full-algebra injectivity of the dual,
its exact Gaussian symbol, and the fermionic CP/dual-positivity equivalence.
The dual is generally subnormalized, not a density matrix. -/
theorem fermionic_duality {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n))
    (hlinear : ComplexLinear E) (hparity : ParityPreserving s E) :
    (∀ F : Superop (Qubits n) (Qubits n), ComplexLinear F → ParityPreserving s F →
      fermionicDual s E = fermionicDual s F → E = F) ∧
    (LinearCompletelyPositive E ↔ (fermionicDual s E).PosSemidef) ∧
    (∀ K : GrassmannKernel n, HasGrassmannKernel s E K →
      doubleSymbol s (fermionicDual s E) = (K.C / (2 : ℂ) ^ (2 * n)) •
        grassExp (kernelAction K (blockVars (2 * n) 2 0) (blockVars (2 * n) 2 1))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
