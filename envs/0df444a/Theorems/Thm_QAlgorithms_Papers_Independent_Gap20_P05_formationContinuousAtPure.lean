-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_formationContinuousAtPure
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.formationContinuousAtPure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:12:02.849763+00:00
-- url     : https://prove2.me/theorems/55e3a183-0682-471c-b767-a9761d556620
-- title:
--   Proposition 6: continuity of countable formation at pure states
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   Here $E_F(\rho)$ is the infimum of $\sum_i p_i E(|u_i\rangle\langle u_i|)$ over countable normalized pure-state decompositions $\rho=\sum_i p_i|u_i\rangle\langle u_i|$ converging in trace norm. Components need not satisfy any energy constraint, and the infimum need not be attained.
--
--   Let $M>0$, let $\sigma\in S_M$ be pure, and let $\rho_k\in S_M$ be arbitrary states with $\|\rho_k-\sigma\|_1\to0$. The formation values of the limit and approximants are finite and
--
--   $$\lim_{k\to\infty}|E_F(\rho_k)-E_F(\sigma)|=0.$$
--
--   This establishes continuity of the countable roof at pure energy-constrained limit points.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 9, Proposition 6: continuity of countable E_F at pure states

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

/-- Proposition 6, PDF pp.9--10, (33): continuity of the countable roof at a
PURE energy-bounded limit, with arbitrary mixed energy-bounded approximants. -/
theorem formationContinuousAtPure (h : HamiltonianData) (M : ℝ) (hM : 0 < M)
    (sigma : PureState (ℕ × ℕ)) (hsigma : sigma.val ∈ energyBound h M)
    (rho : ℕ → State (ℕ × ℕ)) (henergy : ∀ k, rho k ∈ energyBound h M)
    (hlim : Tendsto (fun k => traceSize ((rho k).coefficients - sigma.val.coefficients))
      atTop (𝓝 (0 : ℝ≥0∞))) :
    countableFormationBits sigma.val.coefficients < ⊤ ∧ (∀ k, countableFormationBits (rho k).coefficients < ⊤) ∧
    Tendsto (fun k => |(countableFormationBits (rho k).coefficients).toReal -
      (countableFormationBits sigma.val.coefficients).toReal|) atTop (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
