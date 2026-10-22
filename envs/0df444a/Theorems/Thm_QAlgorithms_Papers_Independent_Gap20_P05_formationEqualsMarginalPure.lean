-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_formationEqualsMarginalPure
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.formationEqualsMarginalPure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:14:03.403081+00:00
-- url     : https://prove2.me/theorems/7fed7c7b-716c-431d-ac43-3146a5b0fee3
-- title:
--   Countable formation equals marginal entropy on pure energy-bounded states
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   Here $E_F(\rho)$ is the infimum of $\sum_i p_i E(|u_i\rangle\langle u_i|)$ over countable normalized pure-state decompositions $\rho=\sum_i p_i|u_i\rangle\langle u_i|$ converging in trace norm. Components need not satisfy any energy constraint, and the infimum need not be attained.
--
--   For every $M>0$ and every pure $\sigma\in S_M$,
--
--   $$E_F(\sigma)=E(\sigma).$$
--
--   This identifies the countable roof with the pure-state marginal entropy on the source's stated domain.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 10, §III, unnumbered: countable E_F agrees with E on pure states

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

/-- Unnumbered identification after Proposition 6, PDF p.10: equality of the
countable roof and marginal entropy for pure states in the stated strict sublevel. -/
theorem formationEqualsMarginalPure (h : HamiltonianData) (M : ℝ) (hM : 0 < M)
    (sigma : PureState (ℕ × ℕ)) (hsigma : sigma.val ∈ energyBound h M) :
    countableFormationBits sigma.val.coefficients = marginalEntropy sigma.val.coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
