-- Prove2me | Theorems.Thm_PI_LocMassTypL_lat_basis
-- name    : PI.LocMassTypL.lat_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:24.745481+00:00
-- url     : https://prove2.me/theorems/eaf5e9e0-9331-4394-9149-31b02e319e65
-- title:
--   Loc Mass Typ L: lat basis
-- statement:
--   The Loc Mass Typ L construction uses the lat basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/LatBasis.lean#L9-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/LatBasis.lean#L9-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_LatBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypL
open NumberField IsDedekindDomain

theorem PI.LocMassTypL.lat_basis {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (L : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) (hfg : L.FG)
    (hsp : Submodule.span (v.adicCompletion F) (L : Set (Fin n → v.adicCompletion F)) = ⊤) :
    ∃ A : Matrix (Fin n) (Fin n) (v.adicCompletion F), IsUnit A ∧
      ∀ y, y ∈ L ↔ ∃ c : Fin n → v.adicCompletion F, (∀ i, c i ∈ v.adicCompletionIntegers F) ∧
        y = A.mulVec c := by sorry
