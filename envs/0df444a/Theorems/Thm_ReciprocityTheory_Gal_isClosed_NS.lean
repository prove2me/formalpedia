-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isClosed_NS
-- name    : ReciprocityTheory.Gal.isClosed_NS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:41.750791+00:00
-- url     : https://prove2.me/theorems/7220d889-0142-43ff-8814-341359acdef1
-- title:
--   Gal: is Closed NS
-- statement:
--   The Gal construction uses the is Closed NS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L137-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L137-L137

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable (Ω)

theorem ReciprocityTheory.Gal.isClosed_NS : IsClosed (NS Ω S : Set (G F Ω)) := by sorry
