-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_11_14
-- name    : QubitPhaseEst.eq_11_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:59.680707+00:00
-- url     : https://prove2.me/theorems/c1fa00bf-ac67-45b6-bdc5-42778626d2ae
-- title:
--   Eqs. (11)–(14): a standard basis exists, and in it $\rho^{\otimes N}$ is block diagonal with blocks $(r_+r_-)^J\,T\,\mathrm{diag}((r_+/r_-)^m)\,T^\dagger$
-- statement:
--   For every $N$:
--
--   1. A standard angular-momentum basis $|j,m,\alpha\rangle_z$ of the $N$ qubits exists, with multiplicities $d_j=\binom{2J}{J-j}-\binom{2J}{J-j-1}$.
--   2. Let $0\le r<1$, $\theta,\psi\in\mathbb R$, $\vec n=r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$ and $R=\rho_{\vec n}^{\otimes N}$, and let $r_\pm=\tfrac12(1\pm r)$, $J=N/2$. In **every** standard basis, $R$ is block diagonal in $(j,\alpha)$: $\langle j',m',\alpha'|R|j,m,\alpha\rangle=0$ unless $(j',\alpha')=(j,\alpha)$. Within a block,
--
--   $$
--   \langle j,m',\alpha|R|j,m,\alpha\rangle=(r_+r_-)^J\Bigl(T\,\mathrm{diag}\bigl((r_+/r_-)^{\mu}\bigr)_{\mu=-j}^{j}\,T^\dagger\Bigr)_{m',m},\qquad T=e^{-i\psi J_z}e^{-i\theta J_y},
--   $$
--
--   with $J_z,J_y$ in the spin-$j$ representation.
--
--   This is the decomposition (11)–(13) of $\rho_{\vec n}^{\otimes N}$ into irreducible representations of $\mathrm{SU}(2)$, written in the $z$ basis rather than in the basis rotated to $\vec b=\vec n/r$.
--
--   Differences from the source:
--   - generalization: n with no y component → every Bloch vector r(sin θ cos ψ, sin θ sin ψ, cos θ) with 0 ≤ r < 1; reason: at ψ = 0 this is the paper's state; the azimuth enters only through e^{−iψJ_z}
--   - encoding: R_n = Σ_j (r₊r₋)^J Σ_α U_{j,α} τ_{j,1} U_{j,α}† in the rotated basis |j,m,α⟩_b → matrix elements in the z basis |j,m,α⟩_z, with |j,m,α⟩_b = T|j,m,α⟩_z; reason: the paper passes to the z basis on pp. 2–3; this form also covers r = 0, where b = n/r is undefined
--   - encoding: T(g_b) = e^{iθJ_y} for some θ → T = e^{−iψJ_z} e^{−iθJ_y}; reason: at ψ = 0 the paper's angle is −θ in this orientation; checked numerically at planning (check4)
--   - encoding: a suitable set of unitary operators U_{j,α} → every family satisfying IsStandardBasis; reason: the paper does not fix the U_{j,α}; the statement holds for each admissible choice
--   - encoding: (r₊r₋)^J and (r₊/r₋)^m with half-integer J, m → real powers of positive reals; reason: r₋ > 0 since r < 1
--   - encoding: m the eigenvalue of ½J_z (p. 2, left column) → m the eigenvalue of J_z (SpinIdx.weight); reason: p. 2, right column, says "m being the eigenvalue of J_z", and Eq. (12) runs m from −j to j; the ½ is a slip
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(14), p. 2

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsStandardBasis
import Definitions.Def_QubitPhaseEst_optValue

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **The block-diagonal form of `R_n`, Eqs. (11)–(14).** arXiv:quant-ph/0411133v3, Sec. II,
Eqs. (11)–(14), p. 2. A standard angular-momentum basis of `N` qubits exists, with the multiplicities
`d_j` of (14). In any such basis `R_n = ρ_n^{⊗N}` is block diagonal in `(j, α)`, and its block is
`(r₊r₋)^J T diag((r₊/r₋)^m) T†`, with `T = e^{−iψJ_z} e^{−iθJ_y}` in the spin-`j` representation.

**Formalization Note.** The paper writes the decomposition in the basis rotated to `b = n/r`. Here it
is in the `z` basis `|m, jα⟩ = |j, m, α⟩_z`, through `|j, m, α⟩_b = T|j, m, α⟩_z` (pp. 2–3), and this form
also covers `r = 0`, where `b` is undefined. The factor `T` carries the general Bloch direction; the
paper's "`e^{iθJ_y}` for some `θ`" is `θ ↦ −θ` at `ψ = 0`. -/
theorem eq_11_14 (N : ℕ) :
    (∃ b : SpinIdx N → Qb N → ℂ, IsStandardBasis b) ∧
    ∀ r θ ψ : ℝ, 0 ≤ r → r < 1 → ∀ b : SpinIdx N → Qb N → ℂ, IsStandardBasis b →
      let R := ShadowTomography.UpperBound.tensorPow (blochState (blochVec r θ ψ)) N
      (∀ (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) (i' i : Fin (N - 2 * (k : ℕ) + 1)),
        let T := spinRotZ (N - 2 * (k : ℕ)) ψ * spinRotY (N - 2 * (k : ℕ)) (-θ)
        braket (b ⟨k, (i', α)⟩) R (b ⟨k, (i, α)⟩) =
          (((rPlus r * rMinus r) ^ ((N : ℝ) / 2) : ℝ) : ℂ) *
            (T * Matrix.diagonal (fun l : Fin (N - 2 * (k : ℕ) + 1) =>
              (((rPlus r / rMinus r) ^ spinM (N - 2 * (k : ℕ)) l : ℝ) : ℂ)) * Tᴴ) i' i) ∧
      (∀ s' s : SpinIdx N, ¬ (s'.1 = s.1 ∧ (s'.2.2 : ℕ) = (s.2.2 : ℕ)) →
        braket (b s') R (b s) = 0) := by sorry

end QubitPhaseEst
