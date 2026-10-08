-- Prove2me | Theorems.Thm_VBSDP_Duality_theorem_3_1
-- name    : VBSDP.Duality.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:18.823808+00:00
-- url     : https://prove2.me/theorems/6e5c6be5-40ed-4a5c-b24b-d856b5ef458f
-- title:
--   Theorem 3.1: strong duality and attainment under strict feasibility
-- statement:
--   Let $c\in\mathbb R^m$ and let $F_0,\ldots,F_m$ be symmetric real $n\times n$ matrices. For the primal problem (1) and dual problem (27), either of the following conditions implies equality of extended optimal values:
--
--   1. There is $x$ with $F(x)\succ0$.
--   2. There is a dual feasible $Z\succ0$.
--
--   $$p^*=d^*.$$
--
--   If both strict-feasibility conditions hold, then both optimal sets are nonempty: $X_{\mathrm{opt}}\ne\varnothing$ and $Z_{\mathrm{opt}}\ne\varnothing$.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, Theorem 3.1, continued on p. 65, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi
import Definitions.Def_VBSDP_Duality_pStar
import Definitions.Def_VBSDP_Duality_dStar
import Definitions.Def_VBSDP_Duality_Xopt
import Definitions.Def_VBSDP_Duality_Zopt

namespace VBSDP.Duality

theorem theorem_3_1 {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian) :
    (((∃ x, (lmi F₀ F x).PosDef) ∨
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      pStar c F₀ F = dStar c F₀ F) ∧
    (((∃ x, (lmi F₀ F x).PosDef) ∧
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      (Xopt c F₀ F).Nonempty ∧ (Zopt c F₀ F).Nonempty) := by sorry

end VBSDP.Duality
