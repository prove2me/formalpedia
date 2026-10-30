-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_finite_fibers
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_finite_fibers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:10:04.085002+00:00
-- url     : https://prove2.me/theorems/5f0dae17-6675-489f-a1cc-b3d5849d2220
-- title:
--   Finite ambiguity of recovering sector phases from l-body phases
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $D_l=C_l/\operatorname{Tr}(C_l^2)$ at physical indices. On the torus of legal sector angles, set $F(\theta)_l=\sum_jc_l(j)\theta_j$. Every coefficient $\operatorname{Tr}(D_l\Pi_j)$ is rational, and for every target phase vector $\Phi$,
--   $$\{\theta\in(\mathbb R/2\pi\mathbb Z)^{\lfloor n/2\rfloor+1}:F(\theta)=\Phi\}\text{ is finite}.$$
--   Every preimage satisfies, for some integer vector $(r_l)$,
--   $$\theta_j=\sum_l\operatorname{Tr}(D_l\Pi_j)\bigl(\phi_l+2\pi r_l\bigr)\pmod{2\pi},$$
--   where $\phi_l\in(-\pi,\pi]$ represents $\Phi_l$. Finiteness, rather than injectivity, expresses the ambiguity of recovering sector phases.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 25, Finite ambiguity of recovering sector phases from l-body phases

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P49

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance 100] LieRing.ofAssociativeRing

-- Specialize the frozen generic aliases without declaring new aliases.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "Vec" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Vec (Qubits n))

-- The frozen support predicate takes the support before the operator.

local notation "WireSupported" => QAlgorithms.Papers.Independent.Information100.P69.Supported

/-- PDF p.25, G8–G11: finite fibers, with rational inverse coefficients and the
integer ambiguity retained. The map is not asserted to be injective. -/
theorem phase_finite_fibers (n : ℕ) :
    (∀ (r : Spin n) (j : Spin n), ∃ q : ℚ,
      (Matrix.trace (dualCentral n (2*r.val)*spinProjector n j)).re = (q : ℝ)) ∧
    (∀ Phi : Spin n → Real.Angle,
      {theta : Spin n → Real.Angle | phaseMap n theta=Phi}.Finite) ∧
    (∀ (Phi theta : Spin n → Real.Angle), phaseMap n theta=Phi →
      ∃ z : Spin n → ℤ, ∀ j : Spin n, theta j =
        ((∑ r : Spin n, (Matrix.trace (dualCentral n (2*r.val)*spinProjector n j)).re *
          ((Phi r).toReal + 2*Real.pi*(z r : ℝ)) : ℝ) : Real.Angle)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
