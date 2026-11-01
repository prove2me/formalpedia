-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_21
-- name    : QubitPhaseEst.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:42.553063+00:00
-- url     : https://prove2.me/theorems/b1cc097f-e479-4beb-90fc-237016b431b0
-- title:
--   Eq. (21): $\sum_{m,j\alpha}|\langle m+1,j\alpha|R|m,j\alpha\rangle|$ equals the explicit value with $T^{(j)}=e^{i\theta J_y}$
-- statement:
--   Let $0\le r<1$, $\theta,\psi\in\mathbb R$, $R=\rho_{\vec n}^{\otimes N}$ with $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$, and let $|m,j\alpha\rangle$ be any standard angular-momentum basis. Then, with $r_\pm=\tfrac12(1\pm r)$, $J=N/2$ and $T^{(j)}=e^{i\theta J_y}$,
--
--   $$
--   \sum_{m,j,\alpha}\bigl|\langle m+1,j\alpha|R|m,j\alpha\rangle\bigr|=\sum_{j=\langle\langle N/2\rangle\rangle}^{J}\ \sum_{m=-j}^{j-1}d_j\,(r_+r_-)^J\,\Bigl|\sum_{n}\Bigl(\frac{r_+}{r_-}\Bigr)^{n}T^{(j)}_{m+1,n}\,T^{(j)\dagger}_{n,m}\Bigr|.
--   $$
--
--   In particular the sum does not depend on the azimuth $\psi$ nor on the choice of standard basis.
--
--   Differences from the source:
--   - generalization: n with no y component → every Bloch vector with 0 ≤ r < 1; reason: specializes to the paper at ψ = 0; the value does not depend on ψ
--   - encoding: Σ_{m=−j}^{j} → Σ_{m=−j}^{j−1}; reason: the term m = j involves T_{j+1,n}, which does not exist, and is zero
--   - encoding: (r₊r₋)^J and (r₊/r₋)^n with half-integer exponents → real powers of positive reals; reason: r₋ > 0 since r < 1
--   - encoding: T(g_b) = e^{iθJ_y} "for some θ" (p. 3) → T = e^{iθJ_y} with θ the polar angle of n; reason: the paper's θ is the polar angle up to orientation (±θ), and (21) is unchanged under θ ↦ −θ, since d^j_{mn}(−θ) = (−1)^{m−n} d^j_{mn}(θ) only flips the sign of each inner sum
--   - generalization: the paper's basis |m, jα⟩ = |j, m, α⟩_z, fixed only up to the unitaries U_{j,α} (p. 2) → every family b satisfying IsStandardBasis (orthonormal, J_z eigenvectors, Condon–Shortley J₊ ladder within each (j, α)); reason: the statement holds for each admissible choice, so it specializes to whichever basis the paper uses; such a family exists (QubitPhaseEst.eq_11_14)
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (21), p. 3

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsStandardBasis
import Definitions.Def_QubitPhaseEst_optValue

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (21), second equality chain.** arXiv:quant-ph/0411133v3, Sec. II, Eq. (21), p. 3:
`Σ_{m,j,α} |⟨m+1, jα|R_n|m, jα⟩|` equals the explicit sum over `j` and `m` with the rotation
`T = e^{iθJ_y}`; it depends on the Bloch vector only through `r` and `θ`.

**Formalization Note.** `optValue` keeps the paper's `e^{iθJ_y}`. The block of `R_n` carries
`e^{−iψJ_z} e^{−iθJ_y}` (`QubitPhaseEst.eq_11_14`); neither the sign of `θ` nor `ψ` changes the moduli. -/
theorem eq_21 {N : ℕ} {r θ ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (b : SpinIdx N → Qb N → ℂ)
    (hb : IsStandardBasis b) :
    let R := ShadowTomography.UpperBound.tensorPow (blochState (blochVec r θ ψ)) N
    ∑ k, ∑ α, ∑ i, ‖braket (b (spinTop k α i)) R (b (spinBot k α i))‖ = optValue N r θ := by sorry

end QubitPhaseEst
