-- Prove2me | Theorems.Thm_UpperTheory_Ram_not_dvd_QS_of_notMem_sq
-- name    : UpperTheory.Ram.not_dvd_QS_of_notMem_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:16.960808+00:00
-- url     : https://prove2.me/theorems/32f74625-7612-5cdf-99d9-234b2517f12b
-- title:
--   Ram: not dvd QS of not Mem sq
-- statement:
--   The Ram construction uses the not dvd QS of not Mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/NotSmallIso.lean#L6-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/NotSmallIso.lean#L6-L33

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_NotSmallIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem UpperTheory.Ram.not_dvd_QS_of_notMem_sq :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), H.toHostRaw.Exact → ∀ (E' : Type) [Field E'] [NumberField E'] (_ : E' ≃+* H.E) (P : HeightOneSpectrum (𝓞 E')) (p : ℕ), p.Prime →
      (p : 𝓞 E') ∈ P.asIdeal → (p : 𝓞 E') ∉ P.asIdeal ^ 2 → ¬ p ∣ H.QS ∧ (H.QS : 𝓞 E') ∉ P.asIdeal := by sorry
