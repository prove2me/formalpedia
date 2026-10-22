-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_marginalEntropyContinuous
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.marginalEntropyContinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:09:45.118015+00:00
-- url     : https://prove2.me/theorems/12627f1e-c309-41b5-90a2-a0303056db15
-- title:
--   Proposition 3: energy-constrained continuity of marginal entropy
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For every $M>0$, $E$ is finite on $S_M$ and is continuous there for the trace norm. Equivalently, for arbitrary, possibly mixed, states $\sigma,\sigma_k\in S_M$,
--
--   $$\|\sigma_k-\sigma\|_1\longrightarrow0\quad\Longrightarrow\quad |E(\sigma_k)-E(\sigma)|\longrightarrow0.$$
--
--   This gives a finite real-valued marginal-entropy functional on the energy-constrained domain; it is an entanglement measure only on its pure states.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 5, Proposition 3: energy-constrained continuity of marginal entropy

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

/-- Proposition 3, PDF p.5, (11): finite marginal entropy and real-valued
trace-norm continuity on S_M, including mixed states. -/
theorem marginalEntropyContinuous (h : HamiltonianData) (M : ℝ) (hM : 0 < M) :
    (∀ rho ∈ energyBound h M, marginalEntropy rho.coefficients < ⊤) ∧
    ContinuousOn (fun rho : State (ℕ × ℕ) => (marginalEntropy rho.coefficients).toReal)
      (energyBound h M) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
