-- Prove2me | Theorems.Thm_SpecialRelativity_light_speed_invariant
-- name    : SpecialRelativity.light_speed_invariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T01:48:32.92462+00:00
-- url     : https://prove2.me/theorems/96230221-e64f-5c0a-b3f8-77a69c5b619e
-- title:
--   Light speed invariance: Lorentz transformations preserve the null cone
-- statement:
--   **Light speed invariance — the null cone is preserved.**
--
--   Let `A` be a Lorentz transformation ($A^{T}\eta A = \eta$) and let `u` be a null separation, $\eta(u, u) = 0$ — the separation class of events connected by light signals.
--
--   **Conclusion:** the image separation is again null, $\eta(Au, Au) = 0$.
--
--   In words: every observer related by a Lorentz transformation assigns separation class $\Delta s^2 = 0$ to exactly the same pairs of events, so light rays — the null lines — are carried to light rays: "the speed of light in vacuum is the same for all observers, regardless of the motion of light source or observer". This is the exact geometric form of the second postulate.
--
--   **Formalization note.** Immediate from the definition: $\eta(Au, Au) = (Au)^{T}\eta(Au) = u^{T}(A^{T}\eta A)u = u^{T}\eta u = 0$, using `Matrix.mulVec` for the action of `A` on `u`. The converse direction (a matrix preserving the null cone is a Lorentz transformation up to scale) is not asserted.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file) (principle of light constancy / light speed invariance; Lorentzian-geometry passage on intervals); A. Einstein, Zur Elektrodynamik bewegter Koerper, Annalen der Physik 17 (1905), 891-921

import Mathlib
import Definitions.Def_SpecialRelativity

namespace SpecialRelativity

open Matrix

/-- Milestone: the principle of light speed invariance, in its exact geometric
form.  Lorentz transformations preserve the Minkowski form, hence preserve its
null cone: every separation class `Δs² = 0` — the class of separations
realizable by light signals — is carried to a separation of the same class.
"The speed of light in vacuum is the same for all observers, regardless of the
motion of light source or observer." -/
theorem light_speed_invariant (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsLorentz A)
    (u : Sp) (hu : IsNull u) : IsNull (A.mulVec u) := by
  sorry

end SpecialRelativity
