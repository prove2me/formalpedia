-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSVerma_pderiv_comm__b92bf3ad3e4e
-- name    : P2M_GlobalTheory_CompanionTheory_DSVerma_pderiv_comm__b92bf3ad3e4e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:39.564392+00:00
-- url     : https://prove2.me/theorems/502c8da2-f339-490a-afb9-8af5d96b3958
-- title:
--   P2 M Global Theory Companion Theory DSVerma pderiv comm  b92bf3ad3e4e: P2 M Global Theory Companion Theory DSVerma pderiv comm  b92bf3ad3e4e
-- statement:
--   The P2 M Global Theory Companion Theory DSVerma pderiv comm  b92bf3ad3e4e construction uses the P2 M Global Theory Companion Theory DSVerma pderiv comm  b92bf3ad3e4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L119-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L119-L127

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
open MvPolynomial

theorem P2M_GlobalTheory_CompanionTheory_DSVerma_pderiv_comm__b92bf3ad3e4e {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by sorry

alias «GlobalTheory».«CompanionTheory».«DSVerma».«pderiv_comm'» := P2M_GlobalTheory_CompanionTheory_DSVerma_pderiv_comm__b92bf3ad3e4e
