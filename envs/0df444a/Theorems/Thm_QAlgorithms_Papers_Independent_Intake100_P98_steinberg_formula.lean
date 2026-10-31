-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_steinberg_formula
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.steinberg_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:04:42.126091+00:00
-- url     : https://prove2.me/theorems/18581600-3c89-4da2-89f1-65c2a3075768
-- title:
--   §1.1, equation (14): Steinberg formula specialized to LR coefficients
-- statement:
--   Let $k\ge1$. A partition is a weakly decreasing $k$-tuple of nonnegative integers, padded by zeros. For a triple $x=(\lambda,\mu,\nu)$ assume $|\lambda|+|\mu|=|\nu|$, where $|\lambda|=\sum_i\lambda_i$. Write $c^\nu_{\lambda\mu}$ for the ordinary homogeneous Littlewood–Richardson coefficient.
--
--   Let $S_k$ act by $\sigma(e_i)=e_{\sigma(i)}$, put $\delta=(k-1,k-3,\ldots,1-k)/2$, and let $K(v)$ count the expressions of $v$ as a nonnegative integral sum of the positive roots $e_i-e_j$ with $i<j$. If $\operatorname{inv}(\pi)$ is the inversion count of a permutation, then
--
--   $$
--   c^\nu_{\lambda\mu}=\sum_{\sigma\in S_k}\sum_{\tau\in S_k}
--   (-1)^{\operatorname{inv}(\sigma\tau)}
--   K\bigl(\sigma(\lambda+\delta)+\tau(\mu+\delta)-(\nu+2\delta)\bigr).
--   $$
--
--   This is the homogeneous LR specialization of Steinberg’s formula; the size equality cancels the trace components.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 4, §1.1, equation (14): Steinberg formula specialized to LR coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Equation (14), PDF p.4 (derived from the formula on p.3).
The size equality is essential to cancel trace components. Containment is
not assumed: (14) also gives the zero coefficients outside containment.
Delta is half the positive-root sum and permutation coordinates use inverses. -/
theorem steinberg_formula (k : ℕ) (hk : 0 < k)
    (x : Coordinates k → ℕ) (hx : ∀ b : Fin 3, Antitone (fun i => x (b,i)))
    (hsize : (∑ i, x (0,i)) + (∑ i, x (1,i)) = ∑ i, x (2,i)) :
    (paddedLRCoefficient x : ℤ) = steinbergSum (realTriple x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
