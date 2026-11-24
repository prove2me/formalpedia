-- Prove2me | Theorems.Thm_SensitivityProfileCycle_crossing_215_vertex_window
-- name    : SensitivityProfileCycle.crossing_215_vertex_window
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-24T09:07:28.569485+00:00
-- url     : https://prove2.me/theorems/8592e3c4-dd97-4425-a406-e02b0fedddd8
-- title:
--   Vertex counts for a profile cycle attaining exponent 2.15
-- statement:
--   Suppose a profile cycle has vertex count $K$, period $L$, and return factor $R$. If $R^{43}\le (K^L)^{20}$, then $$85\le K\le12407.$$ This gives a necessary condition for one certificate to attain the campaign threshold. The endpoint values in this interval are possible under the diagonal-product inequality alone. The assertion leaves existence of a qualifying cycle open.
-- source:
--   Derived from the uniform diagonal-product inequality for the profile-cycle certificate, https://prove2.me/theorems/3559fa37-235a-4ae9-92fc-f97a9861b5b3 . The exponent 43/20 comes from https://prove2.me/theorems/d9f3f773-9b62-4684-8705-7695ad1882d7 . The interval bounds are new exact integer consequences of those inputs.

import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.crossing_215_vertex_window (C : SensitivityProfileCycle.Certificate)
    (hc : C.radius^43 ≤ (C.vertices^C.period)^20) :
    85 ≤ C.vertices ∧ C.vertices ≤ 12407 := by sorry
