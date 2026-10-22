-- Prove2me | Theorems.Thm_PTAlgebra_Structure_corollary_45
-- name    : PTAlgebra.Structure.corollary_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:34.332874+00:00
-- url     : https://prove2.me/theorems/4d1d0587-bbb7-44b1-b8bb-a31b5dfdd7f2
-- title:
--   Corollary 45, p. 17 — M as a direct sum of U(α)
-- statement:
--   For every irreducible representation $\varphi^\alpha$ of $S(n-2)$ that occurs in the permutation action on $(\mathbb C^d)^{\otimes(n-2)}$, the span $U(\alpha)$ of Definition 40's operators is a two-sided ideal in $A=A_n^{t_n}(d)$. These ideals are independent and exhaust $M$:
--   $$M=\bigoplus_{\varphi^\alpha\subseteq V_d[S(n-2)]}U(\alpha).$$
--   Thus no non-occurring label contributes a summand, and the sum has unique components.
--
--   This is the ideal decomposition in Theorem 30(a) before identifying the matrix order of each summand.
--
--   **Formalization Note** The family of real orthogonal irreps is complete by $\sum_\alpha(w^\alpha)^2=(n-2)!$, and directness is `iSupIndep` for the occurring subtype.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, p. 17, Corollary 45

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis
open scoped BigOperators

/-- Corollary 45, p. 17: the occurring `U(α)` form the direct sum `M`. -/
theorem corollary_45 {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : IrrepFamily m)
    (hcomplete : ∑ α : F.ι, (F.dim α) ^ 2 = m.factorial) :
    (∀ α : {α : F.ι // Occurs d F α},
      IsIdealOf (Uideal d F α.1) (algA d m)) ∧
    iSupIndep (fun α : {α : F.ι // Occurs d F α} => Uideal d F α.1) ∧
    (⨆ α : {α : F.ι // Occurs d F α}, Uideal d F α.1) = algM d m := by sorry

end PTAlgebra.Structure
