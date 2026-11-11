-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_finite_identity
-- name    : PolynomialPackingMM.IntegerRecursion.finite_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:59.100201+00:00
-- url     : https://prove2.me/theorems/89071945-6c21-4064-98ae-a15829a95034
-- title:
--   Theorem 4.3 — a finite identity from scalar polynomial packings
-- statement:
--   Fix integers $m>n\ge2$. Suppose that for every $a,b,\delta\ge1$ with $n\delta\ge a+2b-1$, there is an SL-PP modulo $\varepsilon$ of $m$ scalar targets, each Full$_{a,b}$ or Mid$_{a,b}$, using $n$ scalar Full$_{a,b+\delta}$ sources. For every real
--
--   $$\tau>\frac{3\log(1+3/(n-1))}{2\log(m/n)},$$
--
--   there is an exact rational bilinear matrix-multiplication identity at some side $v\ge2$ with rank $r<v^\tau$. This connects the entire supplied scalar packing family to a finite identity. **Formalization Note** The family hypothesis belongs to this conditional theorem; it is not an assumption of Corollary 4.4 or the mission goal.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 18 (PDF 19), Theorem 4.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem finite_identity :
  ∀ (m n : ℕ+), n < m → 2 ≤ (n : ℕ) →
  (∀ a b δ : ℕ+, (a : ℕ) + 2 * (b : ℕ) - 1 ≤ (n : ℕ) * δ →
    ∃ choices : Fin (m : ℕ) → Bool,
      HasSLPacking .approximate (mixedTargets m a b 1 1 1 choices)
        (copies n (product (full a ((b : ℕ) + δ)) 1 1 1))) →
  ∀ τ : ℝ, 3 * Real.log (1 + 3 / ((n : ℝ) - 1)) /
      (2 * Real.log ((m : ℝ) / n)) < τ →
    ∃ (v : ℕ+) (r : ℕ), 2 ≤ (v : ℕ) ∧ (r : ℝ) < (v : ℝ) ^ τ ∧
      HasBilinearAlgorithm .exact [matrixProduct v] r := by sorry

end PolynomialPackingMM.IntegerRecursion
