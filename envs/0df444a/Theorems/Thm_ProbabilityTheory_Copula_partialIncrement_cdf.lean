-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_cdf
-- name    : ProbabilityTheory.Copula.partialIncrement_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:54.143477+00:00
-- url     : https://prove2.me/theorems/bef99e7b-3738-43af-9d40-da8ed77e3ebb
-- title:
--   Copula: partial Increment cdf
-- statement:
--   Partial finite differences of a copula CDF are probabilities of partially open boxes:
--   `Δ_s C (a, b) = P(U ≤ b, Uᵢ > aᵢ for i ∈ s)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L94-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L94-L133

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.partialIncrement_cdf (C : Copula d) (a b : Fin d → I) (s : Finset (Fin d))
    (hab : a ≤ b) :
    partialIncrement C.cdf a b s = C.toMeasure.real {x | x ≤ b ∧ ∀ i ∈ s, a i < x i} := by sorry
