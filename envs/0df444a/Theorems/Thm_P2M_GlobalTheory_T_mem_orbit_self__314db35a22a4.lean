-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mem_orbit_self__314db35a22a4
-- name    : P2M_GlobalTheory_T_mem_orbit_self__314db35a22a4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:52.169669+00:00
-- url     : https://prove2.me/theorems/2f1488e5-39a3-47ab-beba-2aff1a722972
-- title:
--   P2 M Global Theory T mem orbit self  314db35a22a4: P2 M Global Theory T mem orbit self  314db35a22a4
-- statement:
--   The P2 M Global Theory T mem orbit self  314db35a22a4 construction uses the P2 M Global Theory T mem orbit self  314db35a22a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/MemOrbitSelfStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/MemOrbitSelfStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelf
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mem_orbit_self__314db35a22a4 : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left), x ∈ orbit G X x := by sorry

alias «GlobalTheory».«T».«mem_orbit_self'» := P2M_GlobalTheory_T_mem_orbit_self__314db35a22a4
