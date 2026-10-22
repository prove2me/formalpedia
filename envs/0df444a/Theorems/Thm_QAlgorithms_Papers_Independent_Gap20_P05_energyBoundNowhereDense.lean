-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_energyBoundNowhereDense
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.energyBoundNowhereDense
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:08:20.3336+00:00
-- url     : https://prove2.me/theorems/6b79d95b-1e22-4835-a8d6-3baa37c3d67d
-- title:
--   The strict energy sublevel is nowhere dense
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For every $M>0$, the strict energy sublevel is nowhere dense in the full trace-norm state space:
--
--   $$\operatorname{int}_{S(H)}\overline{S_M}^{\|\cdot\|_1}=\varnothing.$$
--
--   This locates the energy-constrained domain inside the full state space. Empty sublevels are allowed; the interior is not taken relative to $S_M$.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 5, §III, unnumbered: the energy-bounded set is nowhere dense

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

/-- Unnumbered assertion following (10), PDF pp.4--5: nowhere dense in the
FULL trace-norm state space, including when the sublevel is empty. -/
theorem energyBoundNowhereDense (h : HamiltonianData) (M : ℝ) (hM : 0 < M) :
    interior (closure (energyBound h M)) = ∅ := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
