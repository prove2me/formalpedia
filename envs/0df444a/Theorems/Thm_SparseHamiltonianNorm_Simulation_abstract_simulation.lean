-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_abstract_simulation
-- name    : SparseHamiltonianNorm.Simulation.abstract_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:27.847197+00:00
-- url     : https://prove2.me/theorems/dc65f327-0f03-4694-92ff-1e79595af0b3
-- title:
--   Theorem 15 — Abstract logarithmic-precision Cayley-query simulation
-- statement:
--   There is an absolute $C>0$, uniform in all dimensions and public parameters, with the following property. Let $M=M^\dagger$ act on a finite complex address space, let $V$ be an isometry from a finite complex system space, and assume $d\ge1$, $\Lambda>0$, $t\ge0$, $0<\varepsilon\le1/2$, $V^\dagger M^2V\preceq I/4$, and $L_0\ge\max(1,\|M\|)$. Put $H=2\sqrt d\,\Lambda V^\dagger MV$ and $\tau=t\sqrt d\,\Lambda$.
--
--   A finite circuit, selected from the public parameters and $V$ before $M$, satisfies
--   $$\|A_MJ-Je^{-itH}\|_{\mathrm{op}}\le\varepsilon,\qquad q\le C[\tau+L_0\log(2/\varepsilon)].$$
--   Only the Cayley unitary of $M$ is queried, with all inverse and controlled variants charged. The clean-output error includes the full finite workspace. Arbitrary finite dimensions are represented in binary with unused addresses fixed; no sparse-lift specialization is imposed.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and the stated operators → coordinates in complex Euclidean spaces, explicit operator norms, and operational source definitions; reason: a choice of orthonormal computational coordinates changes no instance or numerical bound
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Theorem 15, p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=24; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_AbstractAccess

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
/-- Li--Wang, Theorem 15, p.24, Eq. (80), under all standing assumptions (61). -/
theorem abstract_simulation :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n e d : ℕ) (Λ t L₀ ε : ℝ) (V : Matrix (Fin e) (Fin n) ℂ),
        1 ≤ d → 0 < Λ → 0 ≤ t → 1 ≤ L₀ → 0 < ε → ε ≤ 1 / 2 →
        V.conjTranspose * V = 1 →
        ∃ (w : ℕ) (c : CayleyCircuit n e w),
          (c.queryCount 0 : ℝ) ≤ C * (t * Real.sqrt d * Λ + L₀ * Real.log (2 / ε)) ∧
          ∀ M : Matrix (Fin e) (Fin e) ℂ,
            M.IsHermitian → CompressedMoment V M → opNorm M ≤ L₀ →
            CleanSimulation w t ε (compressedH d Λ V M) (c.unitary (fun _ => binaryExtension (cayley M))) := by sorry
end SparseHamiltonianNorm.Simulation
