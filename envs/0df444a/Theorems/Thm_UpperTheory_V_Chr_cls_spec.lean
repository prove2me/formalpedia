-- Prove2me | Theorems.Thm_UpperTheory_V_Chr_cls_spec
-- name    : UpperTheory.V.Chr.cls_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:10.612806+00:00
-- url     : https://prove2.me/theorems/f26a50b1-a781-5d5b-9ab9-0f994068f1cb
-- title:
--   Chr: cls spec
-- statement:
--   The Chr construction uses the cls spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L112-L121

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
variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {k Ω}

theorem UpperTheory.V.Chr.cls_spec (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) : σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by sorry
