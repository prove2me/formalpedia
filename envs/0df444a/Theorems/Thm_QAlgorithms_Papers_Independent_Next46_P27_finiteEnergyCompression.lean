-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_finiteEnergyCompression
-- name    : QAlgorithms.Papers.Independent.Next46.P27.finiteEnergyCompression
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:30:48.188034+00:00
-- url     : https://prove2.me/theorems/6b36fc5d-f78d-4320-9c78-551dd5e4eac5
-- title:
--   Finite-energy photon-cutoff approximation in trace norm
-- statement:
--   Let $\rho$ be a full Fock-space density with finite photon-number mean. For $N\in\mathbb N$, set $P_N=\sum_{j<N}|j\rangle\langle j|$, $C_N=P_N\rho P_N$, and $p_N=\sum_{j<N}\langle j|\rho|j\rangle$. Whenever $p_N>0$, write $\widehat\rho_N=C_N/p_N$.
--
--   For every $\varepsilon>0$ there exists $N_0\ge1$ such that for every $N\ge N_0$, $p_N>0$, $\widehat\rho_N$ is a density, the two differences below are trace class, and
--
--   $$\|C_N-\rho\|_1<\varepsilon,\qquad\|\widehat\rho_N-\rho\|_1<\varepsilon.$$
--
--   This makes the appendix's projection approximation precise without assigning trace one to raw compressions or dividing by zero at small cutoffs. No convergence of stationary points is inferred.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 5, Appendix 1: finite-energy cutoff approximation

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.5, Appendix 1: finite-energy states are approximated in trace norm
by raw and normalized photon compressions. Positive retained mass is eventual,
and normalization is only evaluated with that witness. -/
theorem finiteEnergyCompression (rho : B.FockOperator) (hrho : B.IsDensity rho)
    (henergy : A.FiniteEnergy rho) :
    ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∃ hmass : 0 < retainedMass rho N,
        B.IsTraceClass (photonCutoffCompression rho N - rho) ∧
        B.nuclearTraceNorm (photonCutoffCompression rho N - rho) < eps ∧
        B.IsDensity (normalizedCompression rho N hmass) ∧
        B.IsTraceClass (normalizedCompression rho N hmass - rho) ∧
        B.nuclearTraceNorm (normalizedCompression rho N hmass - rho) < eps := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
