-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_16
-- name    : QubitPhaseEst.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:06.606983+00:00
-- url     : https://prove2.me/theorems/74b8364d-bf20-4791-9bf2-efbcca6587d7
-- title:
--   Eq. (16): $\langle c\rangle\le\bigl|\sum\langle\xi\rangle\langle R\rangle\bigr|\le\sum|\langle\xi\rangle\langle R\rangle|\le\sum_{m,j\alpha}|\langle m+1,j\alpha|R|m,j\alpha\rangle|$
-- statement:
--   Let $0\le r<1$, $\theta,\psi\in\mathbb R$, $R=\rho_{\vec n}^{\otimes N}$ with $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$, let $|m,j\alpha\rangle$ be a standard angular-momentum basis and $\xi$ the seed of a covariant POVM. Then
--
--   $$
--   \begin{aligned}
--   \langle c\rangle&\le\Bigl|\sum_{m,j\alpha}\langle m,j\alpha|\xi|m+1,j\alpha\rangle\langle m+1,j\alpha|R|m,j\alpha\rangle\Bigr|\\
--   &\le\sum_{m,j\alpha}\bigl|\langle m,j\alpha|\xi|m+1,j\alpha\rangle\langle m+1,j\alpha|R|m,j\alpha\rangle\bigr|\\
--   &\le\sum_{m,j\alpha}\bigl|\langle m+1,j\alpha|R|m,j\alpha\rangle\bigr|,
--   \end{aligned}
--   $$
--
--   the sums running over the blocks $(j,\alpha)$ and $m=-j,\dots,j-1$. The last bound follows from the positivity of $\xi$ together with its normalization. It is the upper bound on the averaged cosine of every covariant phase measurement.
--
--   Differences from the source:
--   - generalization: n with no y component → every Bloch vector with 0 ≤ r < 1; reason: specializes to the paper at ψ = 0
--   - encoding: Σ_{m,jα} over all m → m from −j to j − 1 (adjacent pairs); reason: the term m = j has no |m+1, jα⟩ and is absent
--   - generalization: the paper's basis |m, jα⟩ = |j, m, α⟩_z, fixed only up to the unitaries U_{j,α} (p. 2) → every family b satisfying IsStandardBasis (orthonormal, J_z eigenvectors, Condon–Shortley J₊ ladder within each (j, α)); reason: the statement holds for each admissible choice, so it specializes to whichever basis the paper uses; such a family exists (QubitPhaseEst.eq_11_14)
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (16), p. 3

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsSeed
import Definitions.Def_QubitPhaseEst_avgCost
import Definitions.Def_QubitPhaseEst_IsStandardBasis

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (16).** arXiv:quant-ph/0411133v3, Sec. II, Eq. (16), p. 3: for every seed `ξ`,
`⟨c⟩ ≤ |Σ_{m,jα} ⟨m, jα|ξ|m+1, jα⟩⟨m+1, jα|R_n|m, jα⟩| ≤ Σ_{m,jα} |⟨m, jα|ξ|m+1, jα⟩⟨m+1, jα|R_n|m, jα⟩|
≤ Σ_{m,jα} |⟨m+1, jα|R_n|m, jα⟩|`, the last bound following from positivity of `ξ`.

**Formalization Note.** The three inequalities of the printed chain are the three conjuncts.
`(k, α, i)` runs over the adjacent pairs of the standard basis `b`: `spinTop k α i` is `|m+1, jα⟩` and
`spinBot k α i` is `|m, jα⟩`. The Bloch vector is `r (sin θ cos ψ, sin θ sin ψ, cos θ)`; the paper's case
is `ψ = 0`. -/
theorem eq_16 {N : ℕ} {r θ ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (b : SpinIdx N → Qb N → ℂ)
    (hb : IsStandardBasis b) (ξ : Matrix (Qb N) (Qb N) ℂ) (hξ : IsSeed ξ) :
    let R := ShadowTomography.UpperBound.tensorPow (blochState (blochVec r θ ψ)) N
    avgCost Real.cos R ξ ≤
        ‖∑ k, ∑ α, ∑ i, braket (b (spinBot k α i)) ξ (b (spinTop k α i)) *
          braket (b (spinTop k α i)) R (b (spinBot k α i))‖ ∧
      ‖∑ k, ∑ α, ∑ i, braket (b (spinBot k α i)) ξ (b (spinTop k α i)) *
          braket (b (spinTop k α i)) R (b (spinBot k α i))‖ ≤
        ∑ k, ∑ α, ∑ i, ‖braket (b (spinBot k α i)) ξ (b (spinTop k α i)) *
          braket (b (spinTop k α i)) R (b (spinBot k α i))‖ ∧
      ∑ k, ∑ α, ∑ i, ‖braket (b (spinBot k α i)) ξ (b (spinTop k α i)) *
          braket (b (spinTop k α i)) R (b (spinBot k α i))‖ ≤
        ∑ k, ∑ α, ∑ i, ‖braket (b (spinTop k α i)) R (b (spinBot k α i))‖ := by sorry

end QubitPhaseEst
