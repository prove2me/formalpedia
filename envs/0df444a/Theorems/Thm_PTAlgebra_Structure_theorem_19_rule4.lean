-- Prove2me | Theorems.Thm_PTAlgebra_Structure_theorem_19_rule4
-- name    : PTAlgebra.Structure.theorem_19_rule4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:09.827732+00:00
-- url     : https://prove2.me/theorems/463375dd-9901-4faa-a243-0444eeade611
-- title:
--   Theorem 19, p. 6 — fourth multiplication rule
-- statement:
--   Let $V(\sigma)$ act on $(\mathbb C^d)^{\otimes n}$, and let $t_n$ transpose only the last tensor factor. Suppose $\sigma(n)\ne n$ and $\rho(n)\ne n$. Put $a=\sigma^{-1}(n)$, $p=\rho^{-1}(n)$ and $q=\rho(n)$. Then the fourth composition rule of Theorem 19 is
--   $$V(\sigma)^{t_n}V(\rho)^{t_n}=d^{\delta_{aq}}V((\sigma(q)\ n)\sigma\rho(p\ n))^{t_n}.$$
--   The transpositions $(x\ x)$ in the formula are identities.
--
--   This rule describes the dimension-dependent products of the generators of $M$.
--
--   **Formalization Note** The paper’s site labels are shifted to `Fin n`, with $n=m+2$; the matrix formula uses the last factor. The paper’s “$c,d\ne n$” below the display is read as the already named $p,q\ne n$.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, p. 6, Theorem 19, fourth composition rule

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis QAlgorithms.Schur

/-- Theorem 19, fourth composition rule, p. 6. -/
theorem theorem_19_rule4 {d m : ℕ} (hd : 1 ≤ d)
    (σ ρ : Equiv.Perm (Fin (m + 2)))
    (hσ : σ (Fin.last (m + 1)) ≠ Fin.last (m + 1))
    (hρ : ρ (Fin.last (m + 1)) ≠ Fin.last (m + 1)) :
    ptLast (tensorPermutation d (m + 2) σ) *
      ptLast (tensorPermutation d (m + 2) ρ) =
    (if σ⁻¹ (Fin.last (m + 1)) = ρ (Fin.last (m + 1))
      then (d : ℂ) else 1) •
      ptLast (tensorPermutation d (m + 2)
        (Equiv.swap (σ (ρ (Fin.last (m + 1)))) (Fin.last (m + 1)) *
          σ * ρ * Equiv.swap (ρ⁻¹ (Fin.last (m + 1))) (Fin.last (m + 1)))) := by sorry

end PTAlgebra.Structure
