-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_noSeparableBall
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.noSeparableBall
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:05:30.404274+00:00
-- url     : https://prove2.me/theorems/652b8fa9-0968-4d3b-93da-9bf5dfa24d5e
-- title:
--   Proposition 10: no separable ball under a strict mean-energy bound
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   Let $D$ be the trace-norm closed convex hull of product states. For every $\varepsilon>0$, $M>0$, and $\sigma\in S_M$, there is a state $\rho$ such that
--
--   $$\rho\in S_M,\qquad \rho\notin D,\qquad \|\sigma-\rho\|_1<\varepsilon.$$
--
--   Thus entangled states are dense even within the same strict energy sublevel.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 13, Proposition 10: no separable ball under a strict mean-energy bound (seed paper result)

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

/-- Proposition 10, PDF pp.13--14 (advertised on p.1): entangled states are dense
inside every strict energy sublevel. Entangled means outside the trace-norm closed
convex hull D. The flawed stronger energy inequality in the proof is not asserted. -/
theorem noSeparableBall (h : HamiltonianData) (epsilon M : ℝ)
    (hepsilon : 0 < epsilon) (hM : 0 < M) (sigma : State (ℕ × ℕ))
    (hsigma : sigma ∈ energyBound h M) :
    ∃ rho : State (ℕ × ℕ), rho ∈ energyBound h M ∧
      ¬ IsSeparable rho.coefficients ∧
      traceSize (sigma.coefficients - rho.coefficients) < ENNReal.ofReal epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
