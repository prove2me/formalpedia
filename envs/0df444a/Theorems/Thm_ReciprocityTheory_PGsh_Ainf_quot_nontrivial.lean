-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_quot_nontrivial
-- name    : ReciprocityTheory.PGsh.Ainf.quot_nontrivial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:28.605794+00:00
-- url     : https://prove2.me/theorems/bf30c02c-b9e6-47c7-ab1d-cccb2fd6b9de
-- title:
--   Ainf: quot nontrivial
-- statement:
--   The Ainf construction uses the quot nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfFacts.lean#L85-L86

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.Ainf.quot_nontrivial {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) := by sorry
