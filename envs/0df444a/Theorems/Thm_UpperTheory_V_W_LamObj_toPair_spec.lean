-- Prove2me | Theorems.Thm_UpperTheory_V_W_LamObj_toPair_spec
-- name    : UpperTheory.V.W.LamObj.toPair_spec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:09.844633+00:00
-- url     : https://prove2.me/theorems/b9d07cce-f34b-4cdc-a29d-370ad3ad910f
-- title:
--   Lam Obj: to Pair spec
-- statement:
--   The Lam Obj construction uses the to Pair spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean#L185-L187

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix UpperTheory.V.Alg
open UpperTheory UpperTheory.V UpperTheory.V.W
attribute [instance] GFrame.grp GFrame.top GFrame.tgrp GFrame.cpt GFrame.tdisc GFrame.finV GFrame.gv GFrame.tv GFrame.tgv
  GFrame.cv GFrame.dv GFrame.finT
variable {l : ℕ} [Fact l.Prime]
variable {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n)
attribute [instance] UniversalOrdinaryDeterminantRing.ring UniversalOrdinaryDeterminantRing.alg UniversalOrdinaryDeterminantRing.co
attribute [instance] LamObj.ring LamObj.alg LamObj.co

theorem UpperTheory.V.W.LamObj.toPair_spec (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) (v : F.Vl)
    (i : Fin n) : pushCh (Λ.toPair p : Λ.Λ →+* R) (Λ.κ v i) = (p.ψ v i).comp (F.Iv v).subtype := by sorry
