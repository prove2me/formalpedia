-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_KTransitive_proof_f512545d214c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_KTransitive_proof_f512545d214c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:54:53.031385+00:00
-- url     : https://prove2.me/theorems/1ad0d948-a5cb-5580-9120-fbcfdb69d7e3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume KTransitive proof f512545d214c: P2 M Ground Theory Heights  Heights Finite Covolume KTransitive proof f512545d214c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume KTransitive proof f512545d214c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume KTransitive proof f512545d214c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PKTransitive.lean#L11-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PKTransitive.lean#L11-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PKTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic Matrix
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_KTransitive_proof_f512545d214c (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«KTransitive».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_KTransitive_proof_f512545d214c
