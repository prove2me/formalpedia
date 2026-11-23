-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isClosed_Ine
-- name    : ReciprocityTheory.Gal.isClosed_Ine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:40.217071+00:00
-- url     : https://prove2.me/theorems/1986a4cb-0290-49eb-abaf-cf9b2e47b5c8
-- title:
--   Gal: is Closed Ine
-- statement:
--   The Gal construction uses the is Closed Ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L405-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L405-L413

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

theorem ReciprocityTheory.Gal.isClosed_Ine [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by sorry
