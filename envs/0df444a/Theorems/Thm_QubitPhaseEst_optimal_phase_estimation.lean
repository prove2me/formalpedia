-- Prove2me | Theorems.Thm_QubitPhaseEst_optimal_phase_estimation
-- name    : QubitPhaseEst.optimal_phase_estimation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:21:31.367625+00:00
-- url     : https://prove2.me/theorems/43af0a35-b584-4741-b664-2cbcdc700dd1
-- title:
--   Optimal covariant phase estimation for $N$ qubits in a mixed state: the optimum is Eq. (21), attained by a Susskind–Glogower seed
-- statement:
--   Let $N\ge1$, $0\le r<1$ and $\theta,\psi\in\mathbb R$. Let $\rho=\tfrac12(I+\vec n\cdot\vec\sigma)$ with $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$, and $R=\rho^{\otimes N}$ the state of $N$ identically prepared qubits on which the unknown phase shift $U_\phi=e^{-i\phi J_z}$ acts. For a seed $\xi$ of a covariant POVM write $\langle c\rangle_\xi$ for its averaged cosine, $\langle v\rangle_\xi$ for its averaged periodicized variance and $\langle 1-F\rangle_\xi$ for its averaged Uhlmann infidelity, with a uniform prior on $\phi$. Let $V(N,r,\theta)$ be the value (21). Then:
--
--   1. **Upper bound.** Every seed satisfies $\langle c\rangle_\xi\le V(N,r,\theta)$.
--   2. **Attainment.** For every standard angular-momentum basis and every choice of phases $\gamma$ compensating the phases of $\langle m+1,j\alpha|R|m,j\alpha\rangle$, the Susskind–Glogower operator $\xi_{SG}=\sum_{j,\alpha}|e(j,\alpha)\rangle\langle e(j,\alpha)|$ is a seed and
--
--   $$
--   \langle c\rangle_{\xi_{SG}}=V(N,r,\theta)=\sum_{j=\langle\langle N/2\rangle\rangle}^{J}\sum_{m=-j}^{j-1}d_j(r_+r_-)^J\Bigl|\sum_n\Bigl(\frac{r_+}{r_-}\Bigr)^nT^{(j)}_{m+1,n}T^{(j)\dagger}_{n,m}\Bigr|.
--   $$
--
--   3. **Existence.** A standard basis and compensating phases exist.
--   4. **Both figures of merit.** Such a $\xi_{SG}$ also minimizes the averaged periodicized variance and the averaged Uhlmann infidelity among all seeds: $\langle v\rangle_{\xi_{SG}}\le\langle v\rangle_\xi$ and $\langle 1-F\rangle_{\xi_{SG}}\le\langle 1-F\rangle_\xi$.
--
--   This is the paper's optimal phase estimation for qubits in mixed states, for an arbitrary number of identically prepared copies, with either the fidelity or the periodicized variance as figure of merit.
--
--   Differences from the source:
--   - generalization: n with no y component (ψ = 0) → every Bloch vector r(sin θ cos ψ, sin θ sin ψ, cos θ) with 0 ≤ r < 1; reason: at ψ = 0 this is the paper's statement; the value V does not depend on ψ
--   - reading: phases of ⟨m,jα|ξ|m+1,jα⟩ chosen by Eq. (18) → phases satisfying the compensation condition of the p. 3 prose; reason: the printed sign of (18) is right only for n_y = 0; the prose is what the proof uses
--   - reading: "We consider a covariant measurement" (p. 1) → optimality among covariant seeds (4); reason: this is the paper's own domain; optimality among all POVMs is Holevo's cited theorem [8]
--   - encoding: Σ_{m=−j}^{j} in Eq. (21) → Σ_{m=−j}^{j−1}; reason: the term m = j involves T_{j+1,n}, which does not exist, and is zero
--   - encoding: T(g_b) = e^{iθJ_y} "for some θ" (p. 3) → T = e^{iθJ_y} with θ the polar angle of n; reason: the paper's θ is the polar angle up to orientation (±θ), and (21) is unchanged under θ ↦ −θ, since d^j_{mn}(−θ) = (−1)^{m−n} d^j_{mn}(θ) only flips the sign of each inner sum
--   - encoding: Tr[…] in the averaged cost → real part of the trace; reason: the trace is real for the paper's Hermitian R and ξ
--   - generalization: the paper's basis |m, jα⟩ = |j, m, α⟩_z, fixed only up to the unitaries U_{j,α} (p. 2) → every family b satisfying IsStandardBasis (orthonormal, J_z eigenvectors, Condon–Shortley J₊ ladder within each (j, α)); reason: the statement holds for each admissible choice, so it specializes to whichever basis the paper uses; such a family exists (QubitPhaseEst.eq_11_14)
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (16)–(21), p. 3, with Eqs. (6)–(9), p. 2

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsSeed
import Definitions.Def_QubitPhaseEst_avgCost
import Definitions.Def_QubitPhaseEst_infidCost
import Definitions.Def_QubitPhaseEst_sgSeed
import Definitions.Def_QubitPhaseEst_optValue

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Optimal phase estimation for qubit mixed states.** D'Ariano, Macchiavello, Perinotti,
arXiv:quant-ph/0411133v3, Sec. II, Eqs. (16)–(21), p. 3, with the cost reduction (6)–(9), p. 2. For `N`
qubits, each in the state with Bloch vector `n` of length `r < 1` and polar angle `θ`:

1. every covariant seed has averaged cosine at most the value (21);
2. every Susskind–Glogower seed (19)–(20) with compensating phases is a seed and attains it;
3. a standard basis and compensating phases exist;
4. such a seed also minimizes the averaged periodicized variance and the averaged Uhlmann infidelity.

**Formalization Note.** Every Bloch direction is covered, through the azimuth `ψ`; the paper's case is
`ψ = 0`. Optimality is among covariant seeds (4), as in the paper; optimality among all POVMs is
Holevo's cited theorem. Clause 2 quantifies over every standard basis and every compensating `γ`. -/
theorem optimal_phase_estimation {N : ℕ} (hN : 1 ≤ N) {r θ ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    let ρ := blochState (blochVec r θ ψ)
    let R := ShadowTomography.UpperBound.tensorPow ρ N
    (∀ ξ : Matrix (Qb N) (Qb N) ℂ, IsSeed ξ → avgCost Real.cos R ξ ≤ optValue N r θ) ∧
    (∀ (b : SpinIdx N → Qb N → ℂ) (γ : SpinIdx N → ℝ), IsStandardBasis b → IsCompensating b R γ →
      IsSeed (sgSeed b γ) ∧ avgCost Real.cos R (sgSeed b γ) = optValue N r θ) ∧
    (∃ (b : SpinIdx N → Qb N → ℂ) (γ : SpinIdx N → ℝ), IsStandardBasis b ∧ IsCompensating b R γ) ∧
    (∀ (b : SpinIdx N → Qb N → ℂ) (γ : SpinIdx N → ℝ), IsStandardBasis b → IsCompensating b R γ →
      ∀ ξ : Matrix (Qb N) (Qb N) ℂ, IsSeed ξ →
        avgCost vCost R (sgSeed b γ) ≤ avgCost vCost R ξ ∧
        avgCost (infidCost ρ) R (sgSeed b γ) ≤ avgCost (infidCost ρ) R ξ) := by sorry

end QubitPhaseEst
