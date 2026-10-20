-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_alignedThermalUnitaries
-- name    : QAlgorithms.Papers.Independent.Information100.P44.alignedThermalUnitaries
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:44:34.416022+00:00
-- url     : https://prove2.me/theorems/5ea986cc-9ea8-42bf-979b-675060748d19
-- title:
--   III C unnumbered aligned/no-change thermal operations
-- statement:
--   For any nonzero finite system Hamiltonian $H=\operatorname{diag}(E_i)$ and real inverse temperature, the identity channel is a finite thermal operation and preserves every coherence block. More generally, if a system unitary $V$ commutes with $H$, then $\Phi_V(X)=VXV^\dagger$ is a finite thermal operation. For any energies $a\ne b$ and any density matrix $X$,
--   $$\|\Pi_a\Phi_V(X)\Pi_b\|_{\rm op}=\|\Pi_aX\Pi_b\|_{\rm op}.$$
--   Here the blocks are rectangular matrices between the corresponding energy eigenspaces, and the norm is the L2 operator norm. The result describes aligned tasks without claiming every directional matrix entry remains unchanged.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 11, III C unnumbered aligned/no-change thermal operations

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.11, III C: identity and commuting unitaries are finite TO; every inter-energy
block retains its operator norm under a commuting system unitary. -/
theorem alignedThermalUnitaries {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (beta : ℝ) :
    (IsFiniteThermal E beta (fun X => X) ∧
      ∀ (rho : Mat d), IsDensityMatrix rho → ∀ (a b : ℝ), energyBlock E a b ((fun X => X) rho) = energyBlock E a b rho) ∧
    ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      (V : Mat d) * Matrix.diagonal (fun i => (E i : ℂ)) =
        Matrix.diagonal (fun i => (E i : ℂ)) * (V : Mat d) →
      IsFiniteThermal E beta (conjSuperop (V : Mat d)) ∧
      ∀ (rho : Mat d), IsDensityMatrix rho → ∀ (a b : ℝ), a ≠ b →
        specNorm (energyBlock E a b (conjSuperop (V : Mat d) rho)) =
          specNorm (energyBlock E a b rho) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
