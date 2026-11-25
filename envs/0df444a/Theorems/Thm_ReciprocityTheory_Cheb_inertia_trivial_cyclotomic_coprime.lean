-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_inertia_trivial_cyclotomic_coprime
-- name    : ReciprocityTheory.Cheb.inertia_trivial_cyclotomic_coprime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:56.419631+00:00
-- url     : https://prove2.me/theorems/04fe9226-facc-524a-97e5-7dcefc4166fc
-- title:
--   Cheb: inertia trivial cyclotomic coprime
-- statement:
--   The Cheb construction uses the inertia trivial cyclotomic coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L49-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L49-L77

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.inertia_trivial_cyclotomic_coprime (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    [IsGalois E (CyclotomicField l E)]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l)
    (g : Gal(CyclotomicField l E/E)) (hg : g ∈ P.asIdeal.inertia Gal(CyclotomicField l E/E)) : g = 1 := by sorry
