-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CutMP_En_om_sub__2fc4dbc9d380
-- name    : P2M_Formalism_FourierDecayAlt_P_CutMP_En_om_sub__2fc4dbc9d380
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:02.547868+00:00
-- url     : https://prove2.me/theorems/098be11d-0229-417d-8fbe-1a84496f92aa
-- title:
--   P2 M Formalism Fourier Decay Alt P Cut MP En om sub  2fc4dbc9d380: P2 M Formalism Fourier Decay Alt P Cut MP En om sub  2fc4dbc9d380
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Cut MP En om sub  2fc4dbc9d380 construction uses the P2 M Formalism Fourier Decay Alt P Cut MP En om sub  2fc4dbc9d380 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnFibMem.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnFibMem.lean#L12-L16

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En

theorem P2M_Formalism_FourierDecayAlt_P_CutMP_En_om_sub__2fc4dbc9d380 {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by sorry

alias «Formalism».«FourierDecayAlt».«P».«CutMP».«En».«om_sub'» := P2M_Formalism_FourierDecayAlt_P_CutMP_En_om_sub__2fc4dbc9d380
