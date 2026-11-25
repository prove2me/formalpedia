-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_le_one_iff
-- name    : ReciprocityTheory.Gal.smul_valuation_le_one_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:10.010802+00:00
-- url     : https://prove2.me/theorems/65edcc7a-2f12-4166-89b3-afc9c352efcf
-- title:
--   Gal: smul valuation le one iff
-- statement:
--   The Gal construction uses the smul valuation le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L85-L94

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem ReciprocityTheory.Gal.smul_valuation_le_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y ≤ 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) ≤ 1 := by sorry
