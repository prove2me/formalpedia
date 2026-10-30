-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_sector_average_energy
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.sector_average_energy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:05:53.436341+00:00
-- url     : https://prove2.me/theorems/8ef156c1-f8da-411f-8265-c3e4ebf2efea
-- title:
--   Sector average energy and locality, Eq.(7), Appendix E
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Fix $0\le k\le n$. For Hermitian $H$, put $E_j=\operatorname{Tr}(H\Pi_j)/\operatorname{Tr}(\Pi_j)$ and $q_l=\operatorname{Tr}(HC_l)/\operatorname{Tr}(C_l^2)$. If $H$ is a finite sum of terms supported on at most $k$ wires, without any symmetry assumption, then
--   $$E_j=\sum_{l=0}^{2\lfloor k/2\rfloor}q_lc_l(j).$$
--   Thus $E_j$ is the restriction of a real polynomial of degree at most $\lfloor k/2\rfloor$ in $j(j+1)$. For invariant Hermitian $H$ and $k\ge2$, reachability of $e^{-itH}$ for every real $t$ is equivalent to the existence of real coefficients in this expansion; in that case the displayed canonical coefficients work. The sector-energy functions obtained from $k$-local Hermitian sums comprise every function on the legal spins exactly when $\lfloor k/2\rfloor=\lfloor n/2\rfloor$.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 3, Sector average energy and locality, Eq.(7), Appendix E

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

/-- PDF pp.3,22, E3–E6: the first assertion has no symmetry hypothesis.
For invariant Hamiltonians the expansion is equivalent to every-time reachability. -/
theorem sector_average_energy (n k : ℕ) (hk : k ≤ n) :
    (∀ H : Op n, H.IsHermitian → H ∈ localSum n k →
      (∀ j : Spin n, sectorMeanEnergy H j =
        ∑ r : Fin (k/2+1), energyCoeff H (2*r.val)*centralEigenvalue n (2*r.val) j) ∧
      ∃ p : Polynomial ℝ, p.natDegree ≤ k/2 ∧
        ∀ j : Spin n, sectorMeanEnergy H j = p.eval (spin n j*(spin n j+1))) ∧
    (2 ≤ k → ∀ H : Op n, H.IsHermitian → RotationInvariant H →
      ((∀ t : ℝ, evolve H t ∈ localGroup n k) ↔
        ∃ q : Fin (k/2+1) → ℝ, ∀ j : Spin n,
          sectorMeanEnergy H j = ∑ r : Fin (k/2+1), q r * centralEigenvalue n (2*r.val) j) ∧
      ((∀ t : ℝ, evolve H t ∈ localGroup n k) →
        ∀ j : Spin n, sectorMeanEnergy H j =
          ∑ r : Fin (k/2+1), energyCoeff H (2*r.val)*centralEigenvalue n (2*r.val) j)) ∧
    ((∀ f : Spin n → ℝ, ∃ H : Op n, H.IsHermitian ∧ H ∈ localSum n k ∧ sectorMeanEnergy H=f) ↔
      k/2=n/2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
