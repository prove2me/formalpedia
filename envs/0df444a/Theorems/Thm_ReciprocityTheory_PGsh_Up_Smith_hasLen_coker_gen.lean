-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_hasLen_coker_gen
-- name    : ReciprocityTheory.PGsh.Up.Smith.hasLen_coker_gen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:45.767171+00:00
-- url     : https://prove2.me/theorems/69de7c97-95a2-5668-9ee9-5750fa32ae48
-- title:
--   Smith: has Len coker gen
-- statement:
--   The Smith construction uses the has Len coker gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpSmith.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpSmith.lean#L162-L165

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.Smith.hasLen_coker_gen (hv : v.Integers R) {b : ℕ} {ι : Type} [Fintype ι] (g : ι → Fin b → R) :
    HasLen v R ((Fin b → R) ⧸ Submodule.span R (Set.range g))
      (∏ i, v (algebraMap R C ((smith_gen hv b g).choose i))) := by sorry
