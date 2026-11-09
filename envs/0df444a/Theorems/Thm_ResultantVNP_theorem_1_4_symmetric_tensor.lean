-- Prove2me | Theorems.Thm_ResultantVNP_theorem_1_4_symmetric_tensor
-- name    : ResultantVNP.theorem_1_4_symmetric_tensor
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:38:52.069736+00:00
-- url     : https://prove2.me/theorems/9addfaec-e8e2-460a-ab7d-2af36aa8281e
-- title:
--   Theorem 1.4, tensor-determinant clause — poly-size circuits for symmetric $\mathrm{Det}_n$ imply $\mathrm{VP}=\mathrm{VNP}$
-- statement:
--   In fact, the same conclusion as Theorem 1.4 already holds if poly($n$)-size arithmetic circuits over $\mathbb C$ exist for the family of tensor determinants $\{\mathrm{Det}_n(A)\}_{n\ge1}$ restricted to symmetric tensors $A$ of order three (one variable per unordered triple of indices): then $\mathrm{VP}=\mathrm{VNP}$.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: poly(n)-size arithmetic circuits over ℂ → HasPolySizeCircuits: ∃ c, ∀ n ≥ 1, a fan-in-two circuit with complex constants and at most c·n^c + c gates computes the polynomial; reason: Section 3.1 conventions; c·n^c + c dominates every polynomial; size only, as printed
--   - encoding: VP and VNP → sets of PolyFamily (number of variables, p_n over Fin (nvars n)); VNP with g_n on exactly nvars n + q n variables; reason: Section 3.1 definitions
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.4, tensor-determinant clause, p.6 (proof p.17)

import Mathlib
import Definitions.Def_ResultantVNP_symTensorDet
import Definitions.Def_ResultantVNP_HasPolySizeCircuits
import Definitions.Def_ResultantVNP_VNP

namespace ResultantVNP

/-- **Theorem 1.4, tensor-determinant clause.** The same conclusion `VP = VNP` already holds if
poly(n)-size circuits exist for the family of tensor determinants `{Det_n(A)}_{n≥1}` restricted to
symmetric tensors `A` of order three.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.4, tensor-determinant clause, p.6 (proof p.17).

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. Symmetric tensors have one variable per unordered triple of indices (`symTensorDet`). -/
theorem theorem_1_4_symmetric_tensor (𝓡 : ResultantSystem)
    (h : HasPolySizeCircuits (fun n => MvPolynomial.map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))) :
    VP = VNP := by sorry

end ResultantVNP
