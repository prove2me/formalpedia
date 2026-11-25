-- Prove2me | Theorems.Thm_UpperTheory_cmDatum_natCast_mem_heightOneSpectrum_iff
-- name    : UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:13.940674+00:00
-- url     : https://prove2.me/theorems/e057bb15-522c-5c93-8c3d-80baaca797e7
-- title:
--   Upper Theory: cm Datum nat Cast mem height One Spectrum iff
-- statement:
--   The Upper Theory construction uses the cm Datum nat Cast mem height One Spectrum iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumNatCastMemHeightOneSpectrumIff.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumNatCastMemHeightOneSpectrumIff.lean#L17-L25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_CmDatumNatCastMemHeightOneSpectrumIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC IsDedekindDomain

theorem UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff :
    ∀ {φ : Frame} (H : HostRaw φ) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)),
      (((H.QS : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∈ H.small) ∧
      (((H.condN : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∣ H.condN) := by sorry
