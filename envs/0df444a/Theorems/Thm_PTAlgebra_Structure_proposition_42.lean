-- Prove2me | Theorems.Thm_PTAlgebra_Structure_proposition_42
-- name    : PTAlgebra.Structure.proposition_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:10.119874+00:00
-- url     : https://prove2.me/theorems/8b1b2117-5dbf-40db-bc68-5ca92ae401d6
-- title:
--   Proposition 42, pp. 15–16 — occurrence and span of M
-- statement:
--   For each irreducible representation $\varphi^\alpha$ of $S(n-2)$, Definition 40 gives a family $u^{ab}_{ij}(\alpha)$. Proposition 42 says that all these operators are nonzero exactly when $\varphi^\alpha$ occurs in the permutation representation on $(\mathbb C^d)^{\otimes(n-2)}$; equivalently, at least one is nonzero exactly when it occurs. The occurring families span the whole ideal:
--   $$M=\sum_{\varphi^\alpha\subseteq V_d[S(n-2)]}U(\alpha).$$
--   Here $U(\alpha)$ is the complex span of the operators with that irrep label.
--
--   This identifies which irreducible labels actually contribute to $M$ before their directness is established.
--
--   **Formalization Note** The real orthogonal irrep family is assumed complete by $\sum_\alpha(w^\alpha)^2=(n-2)!$. The occurrence test is a nonzero intertwiner into the action on the first $n-2$ factors, with no additional tensor factors.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, pp. 15–16, Proposition 42

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis
open scoped BigOperators

/-- Proposition 42(a,b), pp. 15–16. -/
theorem proposition_42 {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : IrrepFamily m)
    (hcomplete : ∑ α : F.ι, (F.dim α) ^ 2 = m.factorial) :
    (∀ α : F.ι,
      (Occurs d F α ↔
        ∀ (a b : Fin (m + 1)) (i j : Fin (F.dim α)), uOp d F α a b i j ≠ 0) ∧
      (Occurs d F α ↔
        ∃ (a b : Fin (m + 1)) (i j : Fin (F.dim α)), uOp d F α a b i j ≠ 0)) ∧
    (⨆ α : {α : F.ι // Occurs d F α}, Uideal d F α.1) = algM d m := by sorry

end PTAlgebra.Structure
