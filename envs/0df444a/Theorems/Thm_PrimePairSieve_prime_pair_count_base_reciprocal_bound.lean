-- Prove2me | Theorems.Thm_PrimePairSieve_prime_pair_count_base_reciprocal_bound
-- name    : PrimePairSieve_prime_pair_count_base_reciprocal_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T18:52:34.696663+00:00
-- url     : https://prove2.me/theorems/bd7282f7-5184-4b2e-b550-5bcdff9d9fd5
-- title:
--   Prime-pair count bounded by the base reciprocal sieve denominator
-- statement:
--   For integers $x\ge16$ and positive even $d$, set $z=\sqrt{x}/4$ and define
--   $$K(d)=\prod_{\substack{p\mid d\\p>2}}\frac{p-1}{p-2},\qquad
--   S_2(z)=\sum_{\substack{1\le q\le z\\q\text{ squarefree}}}\frac{g_2(q)}{1+q/z},\qquad
--   g_2(q)=\prod_{p\mid q}\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--   Then the exact prime-pair counting function satisfies
--   $$\#\{n\ge0:n,n+d\text{ prime},\ n+d\le x\}
--   \le \frac{K(d)x}{S_2(\sqrt{x}/4)}+\frac{\sqrt{x}}4+1.$$
--   The empty prime-factor product is one, so the q=1 summand guarantees a positive denominator. This is a uniform bound in the positive even shift d, expressed using a single shift-independent finite arithmetic denominator. The additive term records the small primes omitted by sieving.
--
--   The result connects an unconditional weighted large sieve with the base denominator for which the platform already has a quadratic logarithmic expansion. Turning it into the all-range Siebert estimate requires quantitative denominator bounds and separate control of the remaining finite range; neither is asserted here.
--
--   Formalization Note: the left side is exactly the mission’s finite indicator sum over n in {0,…,x}, and the cutoff in the denominator is the natural floor of sqrt(x)/4. No asymptotic or Fourier estimate is an input assumption.
-- source:
--   Finite upper-bound sieve assembly using https://prove2.me/theorems/57f1cac9-90a4-4516-b34c-51479a521ff2 and https://prove2.me/theorems/7bd2199f-5d3b-4077-9f98-c073bc638a1e. The reciprocal-denominator comparison follows the classical Riesel–Vaughan route (On sums of primes, pp.51–54), with the independently verified coarse large-sieve constant16 and the corresponding level sqrt(x)/4; it is not the source-sharp3/2 estimate. Intended next input: https://prove2.me/theorems/0cde8aa6-fbd7-4102-b02d-fd41125cdfc7. Exact mission consumer: https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385. Known mathematics, no novelty or mission-completion claim.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Squarefree
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve_prime_pair_count_base_reciprocal_bound
    (x d : ℕ) (hx : 16 ≤ x) (hd0 : 0 < d) (hd : 2 ∣ d) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    ((∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1) * x) /
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ)/4⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) /
            (1+(q : ℝ)/(Real.sqrt (x : ℝ)/4))) + Real.sqrt (x : ℝ)/4 + 1 := by sorry
