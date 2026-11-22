-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_mem_Ine
-- name    : ReciprocityTheory.Gal.mem_Ine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:54:00.932707+00:00
-- url     : https://prove2.me/theorems/48265ee7-a63d-4d40-b50e-544a4becb1c2
-- title:
--   Gal: mem Ine
-- statement:
--   The Gal construction uses the mem Ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L66-L67

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

theorem ReciprocityTheory.Gal.mem_Ine {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Ine (F := F) A ↔ σ ∈ Inertia (F := F) A := by sorry
