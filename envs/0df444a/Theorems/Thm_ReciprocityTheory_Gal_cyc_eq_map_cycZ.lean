-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_cyc_eq_map_cycZ
-- name    : ReciprocityTheory.Gal.cyc_eq_map_cycZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:20.888425+00:00
-- url     : https://prove2.me/theorems/f3a76047-72a8-40ac-9ec4-27dc738acf68
-- title:
--   Gal: cyc eq map cyc Z
-- statement:
--   The Gal construction uses the cyc eq map cyc Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L95-L97

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
variable (F Ω)

theorem ReciprocityTheory.Gal.cyc_eq_map_cycZ (l : ℕ) [Fact l.Prime] (σ : G F Ω) :
    cyc F Ω l σ = Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      (cycZ F Ω l σ) := by sorry
