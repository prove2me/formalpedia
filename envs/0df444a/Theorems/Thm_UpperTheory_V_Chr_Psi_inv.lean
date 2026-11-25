-- Prove2me | Theorems.Thm_UpperTheory_V_Chr_Psi_inv
-- name    : UpperTheory.V.Chr.Psi_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:14.623287+00:00
-- url     : https://prove2.me/theorems/6dc5e16e-e091-4f17-ac02-e95f6b00c20a
-- title:
--   Chr: Psi inv
-- statement:
--   The Chr construction uses the Psi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L20-L21

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

theorem UpperTheory.V.Chr.Psi_inv (e : ℕ) (ψ : G k Ω →* Oˣ) : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by sorry
