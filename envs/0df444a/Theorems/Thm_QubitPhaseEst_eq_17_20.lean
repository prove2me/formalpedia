-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_17_20
-- name    : QubitPhaseEst.eq_17_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:51.491989+00:00
-- url     : https://prove2.me/theorems/b959bb4d-b486-4dbe-9c42-e13fd07b3d6f
-- title:
--   Eqs. (17)–(20): compensating phases exist, and the Susskind–Glogower seed is admissible and attains (16)
-- statement:
--   Let $0\le r<1$, $\theta,\psi\in\mathbb R$, $R=\rho_{\vec n}^{\otimes N}$ with $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$, and let $|m,j\alpha\rangle$ be a standard angular-momentum basis. Then
--
--   1. there are real phases $\gamma(m,j\alpha)$ that compensate the phases of the matrix elements $\langle m+1,j\alpha|R|m,j\alpha\rangle$, i.e. $e^{i(\gamma(m,j\alpha)-\gamma(m+1,j\alpha))}\langle m+1,j\alpha|R|m,j\alpha\rangle=|\langle m+1,j\alpha|R|m,j\alpha\rangle|$; and
--   2. for every such $\gamma$, the Susskind–Glogower operator $\xi=\sum_{j,\alpha}|e(j,\alpha)\rangle\langle e(j,\alpha)|$, $|e(j,\alpha)\rangle=\sum_m e^{i\gamma(m,j\alpha)}|m,j,\alpha\rangle$, is the seed of a normalized covariant POVM and achieves the bound (16):
--
--   $$
--   \langle c\rangle_\xi=\sum_{m,j\alpha}\bigl|\langle m+1,j\alpha|R|m,j\alpha\rangle\bigr|.
--   $$
--
--   Differences from the source:
--   - reading: phases with χ(m+1,m,jα) = γ(m,jα) − γ(m+1,jα), Eq. (18) → phases satisfying the compensation condition of the p. 3 prose; reason: the printed sign of (18) agrees with the prose for real R (n_y = 0) and fails for general Bloch vectors; the prose is the condition the proof uses
--   - reading: the number of independent linear equations is 2^N − 1 while the unknown phases are 2^N → existence of compensating phases; reason: the counting sentence is the paper's argument for solvability; its conclusion is stated
--   - generalization: n with no y component → every Bloch vector with 0 ≤ r < 1; reason: specializes to the paper at ψ = 0
--   - generalization: the paper's basis |m, jα⟩ = |j, m, α⟩_z, fixed only up to the unitaries U_{j,α} (p. 2) → every family b satisfying IsStandardBasis (orthonormal, J_z eigenvectors, Condon–Shortley J₊ ladder within each (j, α)); reason: the statement holds for each admissible choice, so it specializes to whichever basis the paper uses; such a family exists (QubitPhaseEst.eq_11_14)
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (17)–(20), p. 3

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsSeed
import Definitions.Def_QubitPhaseEst_avgCost
import Definitions.Def_QubitPhaseEst_sgSeed

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eqs. (17)–(20): the Susskind–Glogower seed.** arXiv:quant-ph/0411133v3, Sec. II, Eqs. (17)–(20),
p. 3. Compensating phases exist. For any such `γ`, the operator `ξ = Σ_{j,α}|e(j, α)⟩⟨e(j, α)|` is a seed
and achieves the bound (16).

**Formalization Note.** `IsCompensating` is the p. 3 prose, not the sign of the printed (18). -/
theorem eq_17_20 {N : ℕ} {r θ ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (b : SpinIdx N → Qb N → ℂ)
    (hb : IsStandardBasis b) :
    let R := ShadowTomography.UpperBound.tensorPow (blochState (blochVec r θ ψ)) N
    (∃ γ, IsCompensating b R γ) ∧
    ∀ γ, IsCompensating b R γ →
      IsSeed (sgSeed b γ) ∧
      avgCost Real.cos R (sgSeed b γ) =
        ∑ k, ∑ α, ∑ i, ‖braket (b (spinTop k α i)) R (b (spinBot k α i))‖ := by sorry

end QubitPhaseEst
