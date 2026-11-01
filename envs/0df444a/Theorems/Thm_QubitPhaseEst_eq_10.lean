-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_10
-- name    : QubitPhaseEst.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:41.024719+00:00
-- url     : https://prove2.me/theorems/071b17b8-7240-4567-a8d0-876601e12422
-- title:
--   Eq. (10): $\langle c\rangle=\mathrm{Re}\sum_{m,a,b}\langle m,a|\xi|m+1,b\rangle\langle m+1,b|R|m,a\rangle$
-- statement:
--   Let $R$ and $\xi$ be Hermitian $2^N\times2^N$ matrices. The averaged cosine of the covariant measurement with seed $\xi$ on the state $R$ is
--
--   $$
--   \langle c\rangle=\mathrm{Re}\sum_{\substack{x,y\\ m(y)=m(x)+1}}\langle x|\xi|y\rangle\,\langle y|R|x\rangle,
--   $$
--
--   where $x,y$ run over the computational basis and $m(x)$ is the $J_z$ eigenvalue of $|x\rangle$. In the paper's notation, $\langle c\rangle=\mathrm{Re}\sum_{m,a,b}\langle m,a|\xi|m+1,b\rangle\langle m+1,b|R|m,a\rangle$: only matrix elements between neighbouring $J_z$ eigenspaces contribute.
--
--   Differences from the source:
--   - generalization: R = ρ_n^{⊗N} and ξ a seed → any Hermitian R and ξ; reason: the evaluation of the integral uses only Hermiticity; every density matrix and every seed is Hermitian
--   - encoding: labels |m,a⟩ and |m+1,b⟩ → computational basis vectors x, y with m(y) = m(x) + 1; reason: the computational basis is a basis of J_z eigenvectors, and the sum does not depend on the choice of basis within each eigenspace
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (10), p. 2

import Mathlib
import Definitions.Def_QubitPhaseEst_avgCost

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (10).** arXiv:quant-ph/0411133v3, Sec. II, Eq. (10), p. 2: the averaged cosine is
`⟨c⟩ = Re Σ_{m,a,b} ⟨m, a|ξ|m+1, b⟩⟨m+1, b|R|m, a⟩`.

**Formalization Note.** The labels `(m, a)` and `(m+1, b)` are computational basis vectors `x`, `y`
with `m(y) = m(x) + 1`. The Hermiticity hypotheses hold for every density matrix and seed; they are
what makes the two terms `e^{±iφ′}` of (9) complex conjugates. -/
theorem eq_10 {N : ℕ} (R ξ : Matrix (Qb N) (Qb N) ℂ) (hR : R.IsHermitian) (hξ : ξ.IsHermitian) :
    avgCost Real.cos R ξ = (∑ x, ∑ y, if mz y = mz x + 1 then ξ x y * R y x else 0).re := by sorry

end QubitPhaseEst
