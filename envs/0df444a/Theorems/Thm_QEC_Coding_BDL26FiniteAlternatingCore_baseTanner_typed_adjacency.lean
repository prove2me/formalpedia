-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_baseTanner_typed_adjacency
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.baseTanner_typed_adjacency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:20.76918+00:00
-- url     : https://prove2.me/theorems/35a9d73e-9c99-4332-a328-8ae1663b4e2f
-- title:
--   BDL26 Finite Alternating Core: base Tanner typed adjacency
-- statement:
--   The BDL26 Finite Alternating Core construction uses the base Tanner typed adjacency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L198-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L198-L205

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Mathlib.LinearAlgebra.StdBasis
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteAlternatingCore
open MultiscaleDecoder
open Module

theorem QEC.Coding.BDL26FiniteAlternatingCore.baseTanner_typed_adjacency {u v : BaseTannerVertex}
    (h : baseLevelGraph.skeleton.adjacent u v) :
    (baseTannerKind u = .x ∧ baseTannerKind v = .q) ∨
      (baseTannerKind u = .q ∧ baseTannerKind v = .x) ∨
      (baseTannerKind u = .q ∧ baseTannerKind v = .z) ∨
      (baseTannerKind u = .z ∧ baseTannerKind v = .q) := by sorry
