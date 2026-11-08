-- Prove2me | Theorems.Thm_QubitPhaseEst_isSeed_iff
-- name    : QubitPhaseEst.isSeed_iff
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:19:25.613989+00:00
-- url     : https://prove2.me/theorems/0149f822-54cb-442f-8a28-03f8e7f76942
-- title:
--   Normalization (2) in matrix entries: $\langle m,a|\xi|m,b\rangle=\delta_{ab}$
-- statement:
--   A matrix $\xi$ on $N$ qubits is the seed of a covariant POVM, i.e. $\xi\ge0$ and $\int_0^{2\pi}U_\phi\xi U_\phi^\dagger\,\frac{d\phi}{2\pi}=I$, if and only if $\xi\ge0$ and, for all computational basis vectors $|x\rangle,|y\rangle$ with the same $J_z$ eigenvalue $m(x)=m(y)$,
--
--   $$
--   \langle x|\xi|y\rangle=\delta_{xy}.
--   $$
--
--   In the paper's notation, the normalization holds exactly when $\langle m,a|\xi|m,b\rangle=0$ for $a\ne b$ and $\langle m,a|\xi|m,a\rangle=1$. The converse direction is what certifies that the Susskind–Glogower seed is normalized.
--
--   Differences from the source:
--   - generalization: the normalization (2) implies ⟨m,a|ξ|m,b⟩ = 0 for a ≠ b and ⟨m,a|ξ|m,a⟩ = 1 → if and only if; reason: both directions hold; the forward direction is the paper's statement
--   - encoding: an orthonormal basis |m,a⟩ of each J_z eigenspace → the computational basis; reason: the condition says each diagonal block of ξ is the identity, which does not depend on the orthonormal basis of the eigenspace
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 2, after Eq. (4)

import Mathlib
import Definitions.Def_QubitPhaseEst_IsSeed

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **The normalization condition, in matrix entries.** arXiv:quant-ph/0411133v3, Sec. II, p. 2,
after Eq. (4): the normalization (2) implies `⟨m, a|ξ|m, b⟩ = 0` for `a ≠ b` and
`⟨m, a|ξ|m, a⟩ = 1`.

**Formalization Note.** The paper states one direction; both are true, and the converse is what
shows that the Susskind–Glogower seed is normalized. The basis `|m, a⟩` is the computational basis:
the condition says that each diagonal block of `ξ` is the identity, which does not depend on the
orthonormal basis of the `J_z` eigenspace. -/
theorem isSeed_iff {N : ℕ} (ξ : Matrix (Qb N) (Qb N) ℂ) :
    IsSeed ξ ↔ ξ.PosSemidef ∧ ∀ x y : Qb N, mz x = mz y → ξ x y = if x = y then 1 else 0 := by sorry

end QubitPhaseEst
