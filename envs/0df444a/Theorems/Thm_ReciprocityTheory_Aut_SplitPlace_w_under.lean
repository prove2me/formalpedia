-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_SplitPlace_w_under
-- name    : ReciprocityTheory.Aut.SplitPlace.w_under
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:51.411168+00:00
-- url     : https://prove2.me/theorems/b0d9f3a8-a465-4ec7-b9f7-86d55bb5d6a6
-- title:
--   Split Place: w under
-- statement:
--   The Split Place construction uses the w under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/SplitCoeAlgebraMap.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/SplitCoeAlgebraMap.lean#L89-L93

import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L

theorem ReciprocityTheory.Aut.SplitPlace.w_under (s : SplitPlace L) :
    s.w.asIdeal.comap (algebraMap (𝓞 L⁺) (𝓞 L)) = s.v.asIdeal := by sorry
