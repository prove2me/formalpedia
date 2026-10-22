-- Prove2me | Theorems.Thm_PTAlgebra_Structure_proposition_44_eq6
-- name    : PTAlgebra.Structure.proposition_44_eq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:12.350721+00:00
-- url     : https://prove2.me/theorems/13fcb431-49c8-4dfa-968b-688810b1f254
-- title:
--   Proposition 44, eq. (6), p. 17 — multiplication of the u operators
-- statement:
--   Suppose $\varphi^\alpha$ occurs in $V_d[S(n-2)]$. For the operators of Definition 40, equation (6) of Proposition 44 gives
--   $$u^{ab}_{ij}(\alpha)u^{pq}_{kl}(\alpha)=Q^{bp}_{jk}(\alpha)u^{aq}_{il}(\alpha).$$
--   For a different irrep label $\beta\ne\alpha$, the mixed product $u^{ab}_{ij}(\alpha)u^{pq}_{kl}(\beta)$ is zero. Every site label ranges from $1$ to $n-1$, and the lower indices range over the corresponding representation dimensions.
--
--   This multiplication rule supplies the coefficient matrix that governs the structure and rank of $U(\alpha)$.
--
--   **Formalization Note** The coefficient is $Q^{bp}_{jk}$, with indices $j,k$ as printed in equation (6). Permutation labels are 0-based in Lean. The family is assumed complete by the sum-of-squares identity.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, p. 17, Proposition 44, equation (6)

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis
open scoped BigOperators

/-- Proposition 44, equation (6), p. 17. -/
theorem proposition_44_eq6 {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : IrrepFamily m)
    (hcomplete : ∑ α : F.ι, (F.dim α) ^ 2 = m.factorial) :
    (∀ (α : F.ι), Occurs d F α →
      ∀ (a b p q : Fin (m + 1)) (i j k l : Fin (F.dim α)),
        uOp d F α a b i j * uOp d F α p q k l =
          (Qmat d F α (b, j) (p, k)) • uOp d F α a q i l) ∧
    (∀ (α β : F.ι), Occurs d F α → α ≠ β →
      ∀ (a b p q : Fin (m + 1)) (i j : Fin (F.dim α))
        (k l : Fin (F.dim β)),
        uOp d F α a b i j * uOp d F β p q k l = 0) := by sorry

end PTAlgebra.Structure
