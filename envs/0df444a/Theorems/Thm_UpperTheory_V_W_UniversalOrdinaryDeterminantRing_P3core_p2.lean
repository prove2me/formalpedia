-- Prove2me | Theorems.Thm_UpperTheory_V_W_UniversalOrdinaryDeterminantRing_P3core_p2
-- name    : UpperTheory.V.W.UniversalOrdinaryDeterminantRing.P3core.p2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:50:22.15885+00:00
-- url     : https://prove2.me/theorems/ab29b3e7-3a60-48e9-a395-6e7d6f93ea18
-- title:
--   P3core: p2
-- statement:
--   The P3core construction uses the p2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean#L300-L301

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
attribute [instance] Point.field Point.fin Point.algk Point.algO Point.tower
variable {r}
open UpperTheory.V.W.UniversalOrdinaryDeterminantRing
variable (B : UniversalOrdinaryDeterminantRing r)
variable (J : Ideal B.B)

theorem UpperTheory.V.W.UniversalOrdinaryDeterminantRing.P3core.p2 {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} (H : B.P3core J) : B.P2core J := by sorry
