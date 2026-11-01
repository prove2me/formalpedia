-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_15
-- name    : QubitPhaseEst.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:49.910982+00:00
-- url     : https://prove2.me/theorems/e2bdacfb-a68f-416d-8315-a682f6f96c6c
-- title:
--   Eq. (15): $\langle c\rangle=\mathrm{Re}\sum_{m,j\alpha}\langle m,j\alpha|\xi|m+1,j\alpha\rangle\langle m+1,j\alpha|R|m,j\alpha\rangle$
-- statement:
--   Let $0\le r<1$, $\theta,\psi\in\mathbb R$, $R=\rho_{\vec n}^{\otimes N}$ with $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$, let $|m,j\alpha\rangle$ be a standard angular-momentum basis and $\xi$ a Hermitian matrix. Then the averaged cosine involves only matrix elements inside the invariant subspaces $(j,\alpha)$:
--
--   $$
--   \langle c\rangle=\mathrm{Re}\sum_{j,\alpha}\ \sum_{m=-j}^{j-1}\langle m,j\alpha|\xi|m+1,j\alpha\rangle\,\langle m+1,j\alpha|R|m,j\alpha\rangle.
--   $$
--
--   Differences from the source:
--   - generalization: n with no y component → every Bloch vector with 0 ≤ r < 1; reason: specializes to the paper at ψ = 0
--   - generalization: ξ a seed → any Hermitian ξ; reason: the reduction uses only Hermiticity of ξ; every seed is Hermitian
--   - encoding: Σ_{m,jα} over all m → m from −j to j − 1 (adjacent pairs); reason: the term m = j has no |m+1, jα⟩ and is absent
--   - generalization: the paper's basis |m, jα⟩ = |j, m, α⟩_z, fixed only up to the unitaries U_{j,α} (p. 2) → every family b satisfying IsStandardBasis (orthonormal, J_z eigenvectors, Condon–Shortley J₊ ladder within each (j, α)); reason: the statement holds for each admissible choice, so it specializes to whichever basis the paper uses; such a family exists (QubitPhaseEst.eq_11_14)
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (15), p. 2

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_avgCost
import Definitions.Def_QubitPhaseEst_IsStandardBasis

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (15).** arXiv:quant-ph/0411133v3, Sec. II, Eq. (15), p. 2: in a standard basis only the terms
with the same `(j, α)` survive in (10):
`⟨c⟩ = Re Σ_{m,jα} ⟨m, jα|ξ|m+1, jα⟩⟨m+1, jα|R_n|m, jα⟩`.

**Formalization Note.** `(k, α, i)` runs over the adjacent pairs: `spinTop k α i` is `|m+1, jα⟩` and
`spinBot k α i` is `|m, jα⟩`. The hypothesis on `ξ` holds for every seed; without it `Tr[…]` is not real
and the two exponentials of (9) do not combine. -/
theorem eq_15 {N : ℕ} {r θ ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (b : SpinIdx N → Qb N → ℂ)
    (hb : IsStandardBasis b) (ξ : Matrix (Qb N) (Qb N) ℂ) (hξ : ξ.IsHermitian) :
    let R := ShadowTomography.UpperBound.tensorPow (blochState (blochVec r θ ψ)) N
    avgCost Real.cos R ξ =
      (∑ k, ∑ α, ∑ i, braket (b (spinBot k α i)) ξ (b (spinTop k α i)) *
        braket (b (spinTop k α i)) R (b (spinBot k α i))).re := by sorry

end QubitPhaseEst
