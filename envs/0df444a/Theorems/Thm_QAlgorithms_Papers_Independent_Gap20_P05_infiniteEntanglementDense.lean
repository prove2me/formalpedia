-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_infiniteEntanglementDense
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.infiniteEntanglementDense
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:07:30.853433+00:00
-- url     : https://prove2.me/theorems/3d9d7296-513f-4b78-bb2c-3c08b4ab388e
-- title:
--   Proposition 2: infinite-entanglement pure states are dense
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For every unit vector $\psi$ and every $\varepsilon>0$, there is a unit vector $\phi$ with
--
--   $$\big\||\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|\big\|_1<\varepsilon,\qquad E(|\phi\rangle\langle\phi|)=+\infty.$$
--
--   This is density within all normalized pure states, without an energy constraint. Normalization makes explicit the preceding pure-state convention suppressed by the printed vector quantifier.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 4, Proposition 2: infinite-entanglement pure states are dense

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05

noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

/-- Proposition 2, PDF p.4. Printed: arbitrary vectors; changed to unit vectors
because the surrounding pure-state domain and probability Schmidt weights require
normalization. No energy constraint, and no use of the false distance identity (9). -/
theorem infiniteEntanglementDense (_h : HamiltonianData)
    (psi : Hilbert (ℕ × ℕ)) (hpsi : ‖psi‖ = 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ phi : Hilbert (ℕ × ℕ), ‖phi‖ = 1 ∧
      traceSize (rankOne psi - rankOne phi) < ENNReal.ofReal epsilon ∧
      marginalEntropy (rankOne phi) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
