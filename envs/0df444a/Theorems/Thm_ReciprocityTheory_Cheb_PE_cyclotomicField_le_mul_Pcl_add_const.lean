-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_PE_cyclotomicField_le_mul_Pcl_add_const
-- name    : ReciprocityTheory.Cheb.PE_cyclotomicField_le_mul_Pcl_add_const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:55.407011+00:00
-- url     : https://prove2.me/theorems/bcd36670-40e3-435d-b570-57098d51d003
-- title:
--   Cheb: PE cyclotomic Field le mul Pcl add const
-- statement:
--   The Cheb construction uses the PE cyclotomic Field le mul Pcl add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitB.lean#L25-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitB.lean#L25-L90

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB
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

theorem ReciprocityTheory.Cheb.PE_cyclotomicField_le_mul_Pcl_add_const (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s + C := by sorry
