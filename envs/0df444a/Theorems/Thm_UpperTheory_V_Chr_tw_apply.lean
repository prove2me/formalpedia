-- Prove2me | Theorems.Thm_UpperTheory_V_Chr_tw_apply
-- name    : UpperTheory.V.Chr.tw_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:50.81308+00:00
-- url     : https://prove2.me/theorems/528971d7-42b0-4bc5-bfa4-1152708c7cb3
-- title:
--   Chr: tw apply
-- statement:
--   The Chr construction uses the tw apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L25-L28

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

theorem UpperTheory.V.Chr.tw_apply (e : ℕ) (ψ : G k Ω →* Oˣ) (g : G k Ω) (m : QO l O) :
    twist₂ l (chiO k Ω l O ^ (-(e : ℤ))) g m = ((ψ g : Oˣ) : O) • rho l e ψ g m := by sorry
