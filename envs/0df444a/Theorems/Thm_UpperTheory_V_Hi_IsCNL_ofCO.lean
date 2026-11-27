-- Prove2me | Theorems.Thm_UpperTheory_V_Hi_IsCNL_ofCO
-- name    : UpperTheory.V.Hi.IsCNL.ofCO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:09.422803+00:00
-- url     : https://prove2.me/theorems/4e3fba23-b496-47a6-a2ee-4a7e86040da0
-- title:
--   Is CNL: of CO
-- statement:
--   The Is CNL construction uses the of CO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/HeckeCommRing.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/HeckeCommRing.lean#L27-L30

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_HeckeCommRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.Hi
variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem UpperTheory.V.Hi.IsCNL.ofCO (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R := by sorry
