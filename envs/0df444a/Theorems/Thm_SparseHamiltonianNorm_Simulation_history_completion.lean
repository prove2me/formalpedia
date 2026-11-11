-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_history_completion
-- name    : SparseHamiltonianNorm.Simulation.history_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:14.530257+00:00
-- url     : https://prove2.me/theorems/99cf47a0-494e-4877-9df5-eb04a7f7a3b0
-- title:
--   Lemma 12 — Finite reachable-history unitary completion
-- statement:
--   Let $R\ge1$, $d\ge1$, $\Lambda>0$, $t\ge0$, and $V^\dagger V=I$. The genuine $L^2$ ladder space $F_{R-1}$ is finite dimensional. There exists a unitary on the Hilbert sum $\mathbb C^n\oplus F_{R-1}$ agreeing with $W_t$ on all inputs whose private component lies in $F_{R-2}$, with $F_{-1}=\{0\}$.
--
--   The unitary is chosen before $M$. For every finite Hermitian $M$, every input amplitude vector, every system vector, every unit-circle feedback phase, and every forward slot, the input to the coupling has a representative in that finite space and the completion's output agrees exactly with the continuous coupling. This makes finite circuit adjoints meaningful while retaining the actual continuous histories.
--
--   Differences from the source:
--   - generalization: the source sparse-lift isometry V and forward histories for its sparse-entry M → any isometry between finite complex Euclidean spaces and forward histories for any finite Hermitian M; reason: the coupling and completion use only the isometry property of V, pointwise finite matrices preserve the polynomial-history ladder, and the completion is selected independently of M
--   - encoding: orthogonal sums and the signed index F(R-2) → WithLp 2 direct sum of actual L2 subspaces and integer degree indices; reason: this uses the Euclidean sum norm and retains the R=1 boundary exactly
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 12, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=18; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Routing

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
/-- Li--Wang, Lemma 12, p.18. The completion precedes M, so is independent of it. -/
theorem history_completion (n e d R : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (hR : 1 ≤ R) (hd : 1 ≤ d) (hΛ : 0 < Λ) (ht : 0 ≤ t) (hV : V.conjTranspose * V = 1) :
    FiniteDimensional ℂ (historyLadder e d Λ t ((R : ℤ) - 1)) ∧
    ∃ W : FiniteHistorySpace n e d Λ t R ≃ₗᵢ[ℂ] FiniteHistorySpace n e d Λ t R,
      (∀ x, (finiteHistoryInclusion x).2 ∈ historyLadder e d Λ t ((R : ℤ) - 2) →
        finiteHistoryInclusion (W x) = coupling d Λ t V (finiteHistoryInclusion x)) ∧
      (∀ (M : Matrix (Fin e) (Fin e) ℂ), M.IsHermitian →
        ∀ (a : Fin R → ℂ) (ξ : Vec n) (z : ℂ) (k : ℕ), ‖z‖ = 1 → ∀ hk : k < R,
          let s := routedPrefix d Λ t V M z a ξ k
          ∃ x : FiniteHistorySpace n e d Λ t R,
            finiteHistoryInclusion x = (s.1 ⟨k, hk⟩, z • historyLift t (cayley M) s.2) ∧
            finiteHistoryInclusion (W x) =
              coupling d Λ t V (s.1 ⟨k, hk⟩, z • historyLift t (cayley M) s.2)) := by sorry
end SparseHamiltonianNorm.Simulation
