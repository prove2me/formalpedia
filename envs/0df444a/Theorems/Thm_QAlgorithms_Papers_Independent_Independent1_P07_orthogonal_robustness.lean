-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_orthogonal_robustness
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.orthogonal_robustness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:58.744476+00:00
-- url     : https://prove2.me/theorems/b76758a6-a558-43f9-91bc-f4a928163a12
-- title:
--   Robustness of the orthogonally invariant family
-- statement:
--   For a density matrix $\rho=adP_++bF+cI$ as in Eq. (51), put $f=d\operatorname{Tr}(\rho P_+)$ and $g=\operatorname{Tr}(\rho F)$. Then
--
--   $$N_{ss}(\rho)=N_{ppts}(\rho)=\frac12\max\{|2f-1|-1,\ |2g-1|-1,\ 0\}.$$
--
--   Both robustness quantities retain their variational definitions. The background coincidence of PPT and separability is specific to this family and is attributed by the source to [22].
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §V.B, Eq. (53), PDF p. 8. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement














































/-- Eq. (53), PDF p. 8. Both robustness quantities and their common value;
the separability background for this family is attributed to [22]. -/
theorem orthogonal_robustness {d : ℕ} (hd : 0 < d) (a b c : ℝ)
    (hrho : IsDensityMatrix (orthogonalFamily d hd a b c)) :
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    let rho := orthogonalFamily d hd a b c
    let f := orthogonalF hd rho
    let g := orthogonalG rho
    separableRobustness rho = pptRobustness rho ∧
    separableRobustness rho = max (max (|2*f-1|-1) (|2*g-1|-1)) 0/2 := by sorry


















end QAlgorithms.Papers.Independent.Independent1.P07
