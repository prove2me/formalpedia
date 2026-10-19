-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_orthogonal_negativity
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.orthogonal_negativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:48:00.611019+00:00
-- url     : https://prove2.me/theorems/05dfd436-07ca-495c-9a0a-1f9b6fa98190
-- title:
--   Negativity of orthogonally invariant states
-- statement:
--   Let $d\ge1$, let $F$ swap the two $d$-dimensional factors, and let $P_+$ be the maximally entangled projector. Choose real $a,b,c$ so that $\rho=adP_++bF+cI$ is a density matrix. Set $f=d\operatorname{Tr}(\rho P_+)$ and $g=\operatorname{Tr}(\rho F)$. Then
--
--   $$N(\rho)=\frac{|1-f|}4+\frac{|1+f-2g/d|}4+\frac{|g/d|}2-\frac12.$$
--
--   This computes the measure on the actual family (51), including $d=1$.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §V.B, Eqs. (51)–(52), PDF p. 8. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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













































/-- Eqs. (51)–(52), PDF p. 8, including d = 1. -/
theorem orthogonal_negativity {d : ℕ} (hd : 0 < d) (a b c : ℝ)
    (hrho : IsDensityMatrix (orthogonalFamily d hd a b c)) :
    let rho := orthogonalFamily d hd a b c
    let f := orthogonalF hd rho
    let g := orthogonalG rho
    negativity rho = |1-f|/4+|1+f-2*g/(d : ℝ)|/4+|g/(d : ℝ)|/2-1/2 := by sorry



















end QAlgorithms.Papers.Independent.Independent1.P07
