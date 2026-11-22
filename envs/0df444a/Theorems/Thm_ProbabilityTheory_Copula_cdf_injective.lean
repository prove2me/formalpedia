-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_injective
-- name    : ProbabilityTheory.Copula.cdf_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:42.474168+00:00
-- url     : https://prove2.me/theorems/fceb0ef7-be3c-4478-becb-265f29122678
-- title:
--   Copula: cdf injective
-- statement:
--   The CDF representation is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L54-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L54-L55

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.cdf_injective : Function.Injective (cdf (d := d)) := by sorry
