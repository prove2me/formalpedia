-- Prove2me | Theorems.Thm_QRHLittlewood_littlewood_lower
-- name    : QRHLittlewood.littlewood_lower
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:35:48.845976+00:00
-- url     : https://prove2.me/theorems/2d1a57d1-6f7a-49e9-ac5b-c96941121ac8
-- title:
--   Littlewood lower bound for $L(1,\chi)$ under a zero-free half-plane $\Re s>7/8$
-- statement:
--   There exist constants $c>0$ and $q_0$ with the following property. Let $q\ge q_0$ and let $\chi$ be a primitive real Dirichlet character modulo $q$ such that $L(s,\chi)\neq0$ for every complex $s$ with $\Re s>7/8$. Then
--
--   $$L(1,\chi)\ \ge\ \frac{c}{\log\log q}.$$
--
--   This is Littlewood's lower bound with the generalized Riemann hypothesis for $L(s,\chi)$ replaced by the weaker zero-free half-plane $\Re s>7/8$ for the same character.
--
--   **Formalization Note** $L(1,\chi)$ is compared through its real part; for a real character it is a positive real number.
--
--   **Status note (2026-10-19).** An unconditional version, with the zero-free hypothesis discharged by the formal 7/8 theorem of the OpenAI math release and the explicit constant $0.0621$ for $q\ge10^{100}$, is kernel-checked in [doi:10.5281/zenodo.23459046](https://doi.org/10.5281/zenodo.23459046). The statement above is unchanged.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, Certified harmonic-measure barriers and explicit Littlewood bounds from zero-free regions, https://doi.org/10.5281/zenodo.23400116, Theorem 2(ii) (the statement with unspecified constants is the qualitative form of its explicit bound).

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Real

namespace QRHLittlewood

theorem littlewood_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → (∀ a : ZMod q, (χ a).im = 0) →
      (∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) →
      c / Real.log (Real.log q) ≤ (DirichletCharacter.LFunction χ 1).re := by sorry

end QRHLittlewood
