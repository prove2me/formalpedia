-- Prove2me | Theorems.Thm_P2M_CrystallinePoints_Pd_resSurj_coreD__df1d08f12504
-- name    : P2M_CrystallinePoints_Pd_resSurj_coreD__df1d08f12504
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:10.596059+00:00
-- url     : https://prove2.me/theorems/8c1affd7-92bf-50ae-9957-686aa142930a
-- title:
--   P2 M Crystalline Points Pd res Surj core D  df1d08f12504: P2 M Crystalline Points Pd res Surj core D  df1d08f12504
-- statement:
--   The P2 M Crystalline Points Pd res Surj core D  df1d08f12504 construction uses the P2 M Crystalline Points Pd res Surj core D  df1d08f12504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L61-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L61-L112

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd

theorem P2M_CrystallinePoints_Pd_resSurj_coreD__df1d08f12504.{u} :
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ γ : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, γ q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective γ := by sorry

alias «CrystallinePoints».«Pd».«resSurj_coreD».«» := P2M_CrystallinePoints_Pd_resSurj_coreD__df1d08f12504
