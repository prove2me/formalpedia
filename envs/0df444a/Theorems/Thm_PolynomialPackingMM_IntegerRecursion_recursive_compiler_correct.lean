-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_recursive_compiler_correct
-- name    : PolynomialPackingMM.IntegerRecursion.recursive_compiler_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:19.301674+00:00
-- url     : https://prove2.me/theorems/44104008-9306-4931-9ea1-c565039c008f
-- title:
--   §4.3 — correctness and complete operation bound for the recursive compiler
-- statement:
--   Fix correct finite identity data $D$ with $v\ge2$, $r\ge1$, a positive rational strict rank certificate $t$, and a real $\alpha>\max(2,t)$. With $a=6r+1$ and
--
--   $$C_\alpha=v^\alpha\left(1+\frac{a}{1-r/v^\alpha}\right),$$
--
--   $C_\alpha$ is positive and for every $n\ge1$ the concrete compiler returns a well-formed program which executes successfully on every pair of $n\times n$ integer matrices, returns $AB$, and executes at most $C_\alpha n^\alpha$ arithmetic instructions. This is the operational bridge from a fixed scalar identity to the integer algorithm. **Formalization Note** Successful execution includes every exact-division check; all linear-map arithmetic is counted and padding/cropping have cost zero.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: O(n^alpha) arithmetic cost for the fixed recursive integer identity → C_alpha=v^alpha*(1+(6r+1)/(1-r/v^alpha)), with a=6r+1 and b=0; reason: this instantiates the source recurrence, counting every multiplication, accumulation and exact division, with free input padding and register cropping
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 19 (PDF 20), §4.3, proof of Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_RecursiveCompiler

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem recursive_compiler_correct :
  ∀ (D : IdentityData) (t : ℚ) (α : ℝ),
  2 ≤ D.v → 1 ≤ D.r → D.Correct → D.StrictRank t → (t : ℝ) < α → 2 < α →
  0 < D.boundConstant α ∧
    ∀ n : ℕ, 1 ≤ n → D.RunsCorrectly n ∧
      ((D.compile n).cost : ℝ) ≤ D.boundConstant α * (n : ℝ) ^ α := by sorry

end PolynomialPackingMM.IntegerRecursion
