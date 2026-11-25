-- Prove2me | Theorems.Thm_UpperTheory_V_Chr_shaFam_mono
-- name    : UpperTheory.V.Chr.shaFam_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:21.566523+00:00
-- url     : https://prove2.me/theorems/ecdecabd-78e3-4db6-bd42-060f37dc7dcb
-- title:
--   Chr: sha Fam mono
-- statement:
--   The Chr construction uses the sha Fam mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L42-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L42-L56

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
open UpperTheory UpperTheory.V UpperTheory.V.Chr
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
omit [Fact l.Prime]

theorem UpperTheory.V.Chr.shaFam_mono {m n : ℕ} (h : m ∣ n) : shaFam k Ω m ⊆ shaFam k Ω n := by sorry
