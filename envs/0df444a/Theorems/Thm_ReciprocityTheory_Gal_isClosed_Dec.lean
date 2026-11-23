-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isClosed_Dec
-- name    : ReciprocityTheory.Gal.isClosed_Dec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:23.467797+00:00
-- url     : https://prove2.me/theorems/f295ab21-8a2e-460e-9963-d010fe718fde
-- title:
--   Gal: is Closed Dec
-- statement:
--   The Gal construction uses the is Closed Dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L392-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L392-L403

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

theorem ReciprocityTheory.Gal.isClosed_Dec [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Dec (F := F) A : Set (G F Ω)) := by sorry
