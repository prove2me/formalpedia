-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a
-- name    : P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:20.928356+00:00
-- url     : https://prove2.me/theorems/8159b3a0-c981-5f94-b1d3-72ffecfff582
-- title:
--   P2 M Fixed Order Factor tendsto model Mean  e26385be2e3a: P2 M Fixed Order Factor tendsto model Mean  e26385be2e3a
-- statement:
--   The P2 M Fixed Order Factor tendsto model Mean  e26385be2e3a construction uses the P2 M Fixed Order Factor tendsto model Mean  e26385be2e3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L70-L91
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L70-L91

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) := by sorry

alias «FixedOrderFactor».«tendsto_modelMean'» := P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a
