-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:27.196633+00:00
-- url     : https://prove2.me/theorems/d11128a5-50b2-40f8-ace0-ff3a82e3306f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Domain aeval gen Pt 93dec95d46e3: P2 M Ground Theory Heights  Heights Chart Inc Domain aeval gen Pt 93dec95d46e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Domain aeval gen Pt 93dec95d46e3 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Domain aeval gen Pt 93dec95d46e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L31-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
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
open GroundTheory.Heights₂.Heights.ChartIncDomain
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3 (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g =
      algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncDomain».«aeval_genPt» := P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3
