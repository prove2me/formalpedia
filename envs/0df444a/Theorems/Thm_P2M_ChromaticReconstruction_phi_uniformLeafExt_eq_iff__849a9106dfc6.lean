-- Prove2me | Theorems.Thm_P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6
-- name    : P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:29:23.206405+00:00
-- url     : https://prove2.me/theorems/bb28984b-01b6-4a24-91da-4f6375461b39
-- title:
--   P2 M Chromatic Reconstruction phi uniform Leaf Ext eq iff  849a9106dfc6: P2 M Chromatic Reconstruction phi uniform Leaf Ext eq iff  849a9106dfc6
-- statement:
--   The P2 M Chromatic Reconstruction phi uniform Leaf Ext eq iff  849a9106dfc6 construction uses the P2 M Chromatic Reconstruction phi uniform Leaf Ext eq iff  849a9106dfc6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L102-L149
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L102-L149

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]

theorem P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6 {q : ℕ} (hq : 2 ≤ q)
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Connected) (hH : H.Connected) :
    phi (uniformLeafExt q G) = phi (uniformLeafExt q H) ↔ chromSymm G = chromSymm H := by sorry

alias «ChromaticReconstruction».«phi_uniformLeafExt_eq_iff'» := P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6
