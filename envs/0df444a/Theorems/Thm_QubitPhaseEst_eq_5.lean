-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_5
-- name    : QubitPhaseEst.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:42.730986+00:00
-- url     : https://prove2.me/theorems/4ac9e41b-0ead-4f76-be31-9cf096e466a0
-- title:
--   Eq. (5): reduction of the averaged cost to one integral (corrected: $C(\phi')\to C(-\phi')$)
-- statement:
--   Let $C:\mathbb R\to\mathbb R$ be continuous and $2\pi$-periodic, and let $R$ and $\xi$ be $2^N\times2^N$ matrices. Then the averaged cost (3) of the covariant measurement with seed $\xi$ reduces to a single integral:
--
--   $$
--   \langle C\rangle=\int_0^{2\pi}\frac{d\phi'}{2\pi}\,C(-\phi')\,\mathrm{Tr}\bigl[R\,U_{\phi'}\xi U_{\phi'}^\dagger\bigr].
--   $$
--
--   This expresses $\langle C\rangle$ as the expectation of a cost operator, and is the starting point of the evaluation (9)–(10) of the averaged cosine.
--
--   Differences from the source:
--   - correction: C(φ′) in Eq. (5) → C(−φ′); reason: with C = sin, N = 1, r = 0.8, θ = π/2, ψ = 0.3 and ξ = |e⟩⟨e|, e = (1, i), Eq. (3) gives 0.3821 and the printed (5) gives −0.3821; the two agree for the even costs (6), (7)
--   - reading: a cost C(φ − φ′) of an angle difference → C continuous and 2π-periodic; reason: a function of an angle difference is 2π-periodic; both costs of the paper are continuous
--   - generalization: R = ρ^{⊗N} and ξ a seed → any matrices R and ξ; reason: the identity is a change of variables and uses no property of R or ξ; it specializes to the paper's R and ξ
--   - encoding: Tr[…] → real part of the trace; reason: the trace is real for Hermitian R and ξ, as in every instance of the paper
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (5), p. 2

import Mathlib
import Definitions.Def_QubitPhaseEst_avgCost

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (5), corrected.** arXiv:quant-ph/0411133v3, Sec. II, Eq. (5), p. 2: the double integral (3)
reduces to one integral, `⟨C⟩ = ∫_0^{2π} dφ′/2π C(−φ′) Tr[R U_φ′ ξ U_φ′†]`.

**Formalization Note.** The printed (5) has `C(φ′)`; the correct argument is `−φ′`. The two agree
for the even costs (6), (7). The hypotheses on `C` say that it is a continuous function of an angle
difference; both costs of the paper are. Neither `R` nor `ξ` needs any property. -/
theorem eq_5 {N : ℕ} (C : ℝ → ℝ) (hC : Continuous C) (hper : ∀ φ, C (φ + 2 * Real.pi) = C φ)
    (R ξ : Matrix (Qb N) (Qb N) ℂ) :
    avgCost C R ξ =
      (1 / (2 * Real.pi)) * ∫ φ' in (0 : ℝ)..(2 * Real.pi),
        C (-φ') * (Matrix.trace (R * phaseShift N φ' * ξ * (phaseShift N φ')ᴴ)).re := by sorry

end QubitPhaseEst
