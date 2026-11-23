-- Prove2me | Theorems.Thm_P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09
-- name    : P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:08.204798+00:00
-- url     : https://prove2.me/theorems/9fb4ea63-2fb1-4f67-88c3-e4ecbf3f0ae4
-- title:
--   P2 M Formalism Cyclotomic Norms Cycle Type Finite Order map ne zero  0cc604524e09: P2 M Formalism Cyclotomic Norms Cycle Type Finite Order map ne zero  0cc604524e09
-- statement:
--   The P2 M Formalism Cyclotomic Norms Cycle Type Finite Order map ne zero  0cc604524e09 construction uses the P2 M Formalism Cyclotomic Norms Cycle Type Finite Order map ne zero  0cc604524e09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L69-L70

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}

theorem P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09 (hf : GoodPoly N f) : f.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by sorry

alias «Formalism».«CyclotomicNorms».«CycleTypeFiniteOrder».«map_ne_zero'» := P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09
