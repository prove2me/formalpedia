-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_joint_optimization_sdp
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.joint_optimization_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:54:07.545525+00:00
-- url     : https://prove2.me/theorems/baee740c-7c38-4db6-b962-f78d56ef9f57
-- title:
--   Exact joint resource-and-measurement SDP with attained duality
-- statement:
--   Fix integers $d,N\geq1$, with signals $\sigma_i=d^{-(N-1)}P^+_{A_iB}\otimes I_{\bar A_i}$. The physically attainable entanglement fidelities, optimizing both the normalized resource operator $O$ and Alice's POVM $\{\Pi_i\}$, are exactly the objective values of
--
--   $$\max_{X,\{T_i\}}\frac1{d^2}\sum_i\operatorname{Tr}(T_i\sigma_i),\qquad X\succeq0,\quad\operatorname{Tr}X=d^N,\quad T_i\succeq0,\quad\sum_iT_i=X\otimes I.$$
--
--   A physical protocol maps to $X=O^\dagger O$, $T_i=(O^\dagger\otimes I)\Pi_i(O\otimes I)$ with the same fidelity. Conversely, every feasible $X,\{T_i\}$ is realized in this way by a normalized resource and a POVM, including when $X$ is singular. Both this maximum and the dual minimum are attained and equal:
--
--   $$\min_{\Omega=\Omega^\dagger,\ a\in\mathbb R}\frac{d^N}{d^2}a,\qquad \Omega\succeq\sigma_i\ \text{for all }i,\quad aI-\operatorname{Tr}_B\Omega\succeq0.$$
--
--   This transports joint physical optimization to the SDP without losing attainable resources or measurements.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 4, Eq. (6) and following dual problem

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.4 Eq.(6): exact physical/primal correspondence and attained primal/dual
optima. Singular X is included. The dual factor d^(N-2) is written d^N/d^2,
so N=1 is not corrupted by truncated natural subtraction. -/
theorem joint_optimization_sdp (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    (∀ O : Matrix (Ports d N) (Ports d N) ℂ, ValidResource O →
      ∀ M : Fin N → Matrix (AC d N) (AC d N) ℂ, IsPOVM M →
        PortPrimalFeasible (Oᴴ * O) (fun i => (resourceLift O)ᴴ * M i * resourceLift O) ∧
        primalValue (fun i => (resourceLift O)ᴴ * M i * resourceLift O) =
          QuditFidelity.entanglementFidelity d hd (teleport O M)) ∧
    (∀ X : Matrix (Ports d N) (Ports d N) ℂ,
      ∀ T : Fin N → Matrix (AC d N) (AC d N) ℂ, PortPrimalFeasible X T →
        ∃ O : Matrix (Ports d N) (Ports d N) ℂ,
        ∃ M : Fin N → Matrix (AC d N) (AC d N) ℂ,
          ValidResource O ∧ IsPOVM M ∧ Oᴴ * O = X ∧
          (∀ i, (resourceLift O)ᴴ * M i * resourceLift O = T i)) ∧
    (∃ X : Matrix (Ports d N) (Ports d N) ℂ,
      ∃ T : Fin N → Matrix (AC d N) (AC d N) ℂ,
      ∃ W : Matrix (AC d N) (AC d N) ℂ, ∃ a : ℝ,
        PortPrimalFeasible X T ∧ PortDualFeasible W a ∧
        primalValue T = ((d : ℝ) ^ N / (d : ℝ) ^ 2) * a ∧
        (∀ X' : Matrix (Ports d N) (Ports d N) ℂ,
          ∀ T' : Fin N → Matrix (AC d N) (AC d N) ℂ,
            PortPrimalFeasible X' T' → primalValue T' ≤ primalValue T) ∧
        (∀ W' : Matrix (AC d N) (AC d N) ℂ, ∀ a' : ℝ,
          PortDualFeasible W' a' → ((d : ℝ) ^ N / (d : ℝ) ^ 2) * a ≤
            ((d : ℝ) ^ N / (d : ℝ) ^ 2) * a')) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
