-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_relativeEntanglementContinuous
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.relativeEntanglementContinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:15:43.040778+00:00
-- url     : https://prove2.me/theorems/e4fd8363-d4e5-4dfa-a382-80b6a50f91f4
-- title:
--   Proposition 8: energy-constrained continuity of relative entropy of entanglement
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For each comparison set $C\in\{D,P\}$, let $E_R^C(\rho)=\inf_{\tau\in C}D_2(\rho\|\tau)$, where $D_2$ is the extended quantum relative entropy in bits, $D$ is the trace-norm closed convex hull of product states, and $P$ is the trace-norm closure of states whose partial transpose is a state. The comparison states have no energy constraint.
--
--   For every $M>0$ and each $C\in\{D,P\}$, $E_R^C$ is finite on $S_M$ and continuous there in trace norm. Thus for all states $\sigma,\rho_k\in S_M$,
--
--   $$\|\rho_k-\sigma\|_1\longrightarrow0\quad\Longrightarrow\quad |E_R^C(\rho_k)-E_R^C(\sigma)|\longrightarrow0.$$
--
--   This applies on the whole energy-bounded state domain, including mixed limit states.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 11, Proposition 8: energy-constrained continuity of relative entropy of entanglement

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

/-- Proposition 8, PDF pp.11--12: finite real-valued trace-norm continuity for
E_R with either of the comparison sets D and P, neither energy constrained. -/
theorem relativeEntanglementContinuous (h : HamiltonianData) (M : ℝ) (hM : 0 < M) :
    ∀ ppt : Bool,
      (∀ rho ∈ energyBound h M, comparisonRelativeEntropyBits ppt rho.coefficients < ⊤) ∧
      ContinuousOn (fun rho : State (ℕ × ℕ) =>
        (comparisonRelativeEntropyBits ppt rho.coefficients).toReal) (energyBound h M) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
