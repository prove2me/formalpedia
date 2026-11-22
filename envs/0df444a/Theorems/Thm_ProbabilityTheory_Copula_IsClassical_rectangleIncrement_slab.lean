-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_slab
-- name    : ProbabilityTheory.Copula.IsClassical.rectangleIncrement_slab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:38.232052+00:00
-- url     : https://prove2.me/theorems/abe02381-097a-490a-8d3d-7db09ab885fa
-- title:
--   Is Classical: rectangle Increment slab
-- statement:
--   The Is Classical construction uses the rectangle Increment slab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L78-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L78-L87

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem ProbabilityTheory.Copula.IsClassical.rectangleIncrement_slab (hF : IsClassical F) (b : Fin d → I)
    (i : Fin d) (t : I) :
    rectangleIncrement F (Function.update (fun _ => 0) i t) b =
      F b - F (Function.update b i t) := by sorry
