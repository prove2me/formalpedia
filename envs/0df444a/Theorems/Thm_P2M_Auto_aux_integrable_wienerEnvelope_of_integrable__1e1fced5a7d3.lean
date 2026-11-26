-- Prove2me | Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
-- name    : P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:43.263097+00:00
-- url     : https://prove2.me/theorems/f9335ccc-20ea-5952-878c-a4f15b119ba3
-- title:
--   P2 M Auto aux integrable wiener Envelope of integrable  1e1fced5a7d3: P2 M Auto aux integrable wiener Envelope of integrable  1e1fced5a7d3
-- statement:
--   Radius-independence of envelope integrability on any proper normed additive group equipped
--   with a translation-invariant volume.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L684-L698
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L684-L698

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3 {E F : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddRightInvariant (volume : Measure E)] [NormedAddCommGroup F]
    {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hfr : Integrable (wienerEnvelope f r)) :
    Integrable (wienerEnvelope f s) := by sorry

alias «Auto».«aux_integrable_wienerEnvelope_of_integrable'» := P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
