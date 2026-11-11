-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_sparse_simulation
-- name    : SparseHamiltonianNorm.Simulation.sparse_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:29.648312+00:00
-- url     : https://prove2.me/theorems/0faeaf7c-e51d-42c9-93b1-851634517f72
-- title:
--   Theorem 1 — Sparse Hamiltonian simulation from full norm bounds
-- statement:
--   There are absolute positive constants $C,C'$. Let $1\le d\le N$, $t\ge0$, $\Lambda>0$, $0<\Lambda_{\max}\le\Lambda$, and $0<\varepsilon\le1/2$. For sufficiently fine and sufficiently large public signed fixed-point registers, a finite elementary-gate circuit is chosen before the hidden Hermitian $d$-sparse matrix $H$, its row permutations, and its compatible value tables. The promises are only $\|H\|_{1\to2}\le\Lambda$ and $\|H\|_{\max}\le\Lambda_{\max}$. The same circuit works for every such compatible input and satisfies
--   $$\|A_HJ-Je^{-itH}\|_{\mathrm{op}}\le\varepsilon,$$
--   $$q_F+q_H\le C\left[t\sqrt d\,\Lambda+\sqrt{td\Lambda_{\max}\log(2/\varepsilon)}+\log(2/\varepsilon)\right].$$
--   If $t\Lambda\ge\log(2/\varepsilon)$, the same count is at most $C't\sqrt d\,\Lambda$. At $t=0$ the constructed circuit uses zero calls. Queries include inverse and controlled variants of the original sparse location/value oracles. All work, location, value, clock, and amplification qubits occur in $J$; unused binary addresses are included in the output norm.
--
--   This retains the mixed accuracy term and the complete original time and dimension ranges. It approximates the original arbitrary complex $H$, not just a rounded surrogate.
--
--   Differences from the source:
--   - encoding: entries supplied to sufficiently many value bits of precision → two signed fixed-point coordinates with public error at most min(LambdaMax/4, Lambda/(4 sqrt d), epsilon/(32 t d)) for positive time, Hermitian decoded values, and preserved zeros; reason: entry error gives operator perturbation at most d times that error; publicly inflated rounded norm bounds are at most 5/4 of the input bounds and the target remains the original H
--   - encoding: finite circuits and Eq. (10) for every input, with absolute big-O constants → uniform constants, then public parameters and circuit syntax, then hidden matrices and oracle tables, with an explicit binary clean embedding; reason: this spells out oracle independence, counts every query variant, and measures the full clean-output map without changing the asymptotic scale
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Theorem 1, p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=3; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseAccess

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
open QAlgorithms
/-- Li--Wang, STOC 2027 submission #1383 (October 2026), Theorem 1, p.3,
Eqs. (10)--(11). Constants and the circuit are chosen before the hidden input. -/
theorem sparse_simulation :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
    ∀ (N d : ℕ) (t Λ Λmax ε : ℝ),
      1 ≤ d → d ≤ N → 0 ≤ t → 0 < Λ → 0 < Λmax → Λmax ≤ Λ →
      0 < ε → ε ≤ 1 / 2 →
      ∃ p k : ℕ, SufficientPrecision d t Λ Λmax ε p k ∧
      ∀ p' k' : ℕ, SufficientPrecision d t Λ Λmax ε p' k' →
      ∃ (w : ℕ) (c : SparseCircuit N k' (w + addressBits N)),
        (sparseQueries c : ℝ) ≤ C * simulationScale d t Λ Λmax ε ∧
        (t * Λ ≥ Real.log (2 / ε) → (sparseQueries c : ℝ) ≤ C' * (t * Real.sqrt d * Λ)) ∧
        (t = 0 → sparseQueries c = 0) ∧
        ∀ (H : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → Equiv.Perm (Fin N))
          (table : Fin N → Fin N → Qubits (valueBits k')),
          SparsePromise d Λ Λmax H → ListsSupport d H f → ValueTableFor p' k' H table →
          CleanSimulation w t ε H (c.unitary (sparseOracles f table)) := by sorry
end SparseHamiltonianNorm.Simulation
