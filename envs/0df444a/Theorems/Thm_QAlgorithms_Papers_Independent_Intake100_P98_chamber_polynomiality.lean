-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_chamber_polynomiality
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.chamber_polynomiality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:03:50.834836+00:00
-- url     : https://prove2.me/theorems/42b094dd-b206-48ae-b0c9-b4e88097d335
-- title:
--   Theorem 4.1: polynomiality on the Littlewood–Richardson complex (seed headline)
-- statement:
--   Let $k\ge1$. A partition is a weakly decreasing $k$-tuple of nonnegative integers, padded by zeros. For a triple $x=(\lambda,\mu,\nu)$ assume $|\lambda|+|\mu|=|\nu|$ and $\lambda_i,\mu_i\le\nu_i$ for every $i$, where $|\lambda|=\sum_i\lambda_i$. Write $c^\nu_{\lambda\mu}$ for the ordinary homogeneous Littlewood–Richardson coefficient.
--
--   Let $\mathrm{LR}_k$ be the complex constructed in Definition 2.4 by pulling back the chamber complex of the explicit hive slack matrix $E_k$ along the explicit boundary matrix $B_k$ and intersecting with the partition domain. For every cone $C$ of this complex there is a polynomial $p_C\in\mathbb Q[\lambda_1,\ldots,\lambda_k,\mu_1,\ldots,\mu_k,\nu_1,\ldots,\nu_k]$ such that
--
--   $$
--   c^\nu_{\lambda\mu}=p_C(\lambda,\mu,\nu)\qquad ((\lambda,\mu,\nu)\in C\text{ integral}),\qquad
--   \deg_\lambda p_C,\deg_\mu p_C,\deg_\nu p_C\le {k-1\choose2}.
--   $$
--
--   Each degree is total degree within the indicated block. All lattice boundary points are included. This supplies polynomial pieces on the particular LR complex, rather than merely on fixed rays.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 10, Theorem 4.1: polynomiality on the Littlewood–Richardson complex (seed headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Theorem 4.1, PDF p.10. One rational polynomial for EVERY cone of the
constructed LR complex, including all its integral partition boundary points.
Degree means total degree within each block, not an exact total degree claim. -/
theorem chamber_polynomiality (k : ℕ) (hk : 0 < k) :
    ∀ C ∈ lrComplex k, ∃ p : MvPolynomial (Coordinates k) ℚ,
      BlockDegreeAtMost p (Nat.choose (k-1) 2) ∧
      ∀ x : Coordinates k → ℕ, IntegralDomain x → realTriple x ∈ C →
        MvPolynomial.eval (fun v => (x v : ℚ)) p = (paddedLRCoefficient x : ℚ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
