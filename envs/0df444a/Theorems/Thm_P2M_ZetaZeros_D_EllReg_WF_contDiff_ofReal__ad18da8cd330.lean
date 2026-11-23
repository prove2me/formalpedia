-- Prove2me | Theorems.Thm_P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330
-- name    : P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:08.890731+00:00
-- url     : https://prove2.me/theorems/e3b7746b-164c-4313-b413-ab92bb202cdb
-- title:
--   P2 M Zeta Zeros D Ell Reg WF cont Diff of Real  ad18da8cd330: P2 M Zeta Zeros D Ell Reg WF cont Diff of Real  ad18da8cd330
-- statement:
--   The P2 M Zeta Zeros D Ell Reg WF cont Diff of Real  ad18da8cd330 construction uses the P2 M Zeta Zeros D Ell Reg WF cont Diff of Real  ad18da8cd330 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L272-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L272-L277

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}

theorem P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330 {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := by sorry

alias «ZetaZeros».«D».«EllReg».«WF».«contDiff_ofReal'» := P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330
