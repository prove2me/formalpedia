-- Prove2me | Theorems.Thm_UpperTheory_V_Base_galEmbTop
-- name    : UpperTheory.V.Base.galEmbTop
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:23.037366+00:00
-- url     : https://prove2.me/theorems/743a8399-2884-4e97-9443-232a60faab5d
-- title:
--   Base: gal Emb Top
-- statement:
--   The Base construction uses the gal Emb Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/GalEmbTop.lean#L32-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/GalEmbTop.lean#L32-L69

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_GalEmbTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by sorry
