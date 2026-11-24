-- Prove2me | Theorems.Thm_UpperTheory_V_Base_range_galEmb
-- name    : UpperTheory.V.Base.range_galEmb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:33.199811+00:00
-- url     : https://prove2.me/theorems/8abd6ec0-6242-4f69-a157-2b993e490e11
-- title:
--   Base: range gal Emb
-- statement:
--   The Base construction uses the range gal Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/ConjStableShaFam.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/ConjStableShaFam.lean#L71-L79

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology TensorProduct
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω]
variable [Algebra k E] [IsScalarTower k E Ω]

theorem UpperTheory.V.Base.range_galEmb : (galEmb k E Ω).range = galOf k E Ω := by sorry
