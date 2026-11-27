-- Prove2me | Theorems.Thm_P2M_UpperTheory_V_Chr_V__le_V_2b4a0b8d1ec7
-- name    : P2M_UpperTheory_V_Chr_V__le_V_2b4a0b8d1ec7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:48.348321+00:00
-- url     : https://prove2.me/theorems/adbf9cda-dbed-51fc-b6d0-a84cb858d176
-- title:
--   P2 M Upper Theory V Chr V  le V 2b4a0b8d1ec7: P2 M Upper Theory V Chr V  le V 2b4a0b8d1ec7
-- statement:
--   The P2 M Upper Theory V Chr V  le V 2b4a0b8d1ec7 construction uses the P2 M Upper Theory V Chr V  le V 2b4a0b8d1ec7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L66-L67

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

theorem P2M_UpperTheory_V_Chr_V__le_V_2b4a0b8d1ec7 (N e : ℕ) (ψ : G k Ω →* Oˣ) : V' l N e ψ ≤ V l e ψ := by sorry

alias «UpperTheory».«V».«Chr».«V'_le_V» := P2M_UpperTheory_V_Chr_V__le_V_2b4a0b8d1ec7
