-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_algebraicIndependent_of_prodCongr
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_algebraicIndependent_of_prodCongr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/43e08e49-fe63-47e4-bfc8-3a8ad44a556c
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_algebraicIndependent_of_prodCongr
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_algebraicIndependent_of_prodCongr
    {n : ℕ} {Y : Type u} {ι : Type v}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y)
    (α : ι → Y →₀ ℕ)
    (hind : AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d₀) (α i))) :
    AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d) (α i)) := by sorry
