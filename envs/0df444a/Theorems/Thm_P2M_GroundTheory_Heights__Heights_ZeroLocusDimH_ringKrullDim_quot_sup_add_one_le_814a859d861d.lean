-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:36.004479+00:00
-- url     : https://prove2.me/theorems/67ae55e8-6dc7-465e-996c-ab04578b5f0e
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim quot sup add one le 814a859d861d: P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim quot sup add one le 814a859d86
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim quot sup add one le 814a859d861d construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim quot sup add one le 814a859d861d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L30-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«ringKrullDim_quot_sup_add_one_le» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d
