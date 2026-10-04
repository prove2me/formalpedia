-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_siftedVonMangoldt_le_log_four
-- name    : TaoFivePrimes.sum_siftedVonMangoldt_le_log_four
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-12T16:31:39.726736+00:00
-- url     : https://prove2.me/theorems/58d46c07-3497-436d-b5ec-3af7359b9a74
-- title:
--   Elementary Chebyshev bound for the sifted von Mangoldt weight: $\sum_{n\le N}\Lambda^\sharp_N(n)\le N\log 4$
-- statement:
--   With $\Lambda^{\sharp}_{N}(n)=\Lambda(n)\mathbf 1_{\gcd(n,\lfloor\sqrt N\rfloor^{\sharp})=1}$ the von Mangoldt function sifted of all prime factors up to $\sqrt N$, as in Section 8 of the source,
--
--   $$\sum_{n\le N}\Lambda^{\sharp}_{N}(n)\;\le\;N\log4\;=\;1.3862\ldots\,N .$$
--
--   Every explicit estimate of this kind in the source routes through the Rosser--Schoenfeld inequality $\psi(x)<1.03883\,x$, which rests on an explicit zero-free region together with a numerical verification. The bound above is the elementary alternative: it is weaker by a factor $\log4/1.03883=1.33\ldots$, but it is unconditional and rests only on Chebyshev's estimate $m^{\sharp}\le4^{m}$ for the primorial. It is therefore available wherever a crude upper bound on the sifted prime mass suffices.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 2 (Notation), the sifted von Mangoldt convention Λ_{q_0}(n) = Λ(n) 1_{(n,q_0)=1} with q_0 = (√x)^♯ taken as in Section 8; combined with the elementary Chebyshev bound n^♯ ≤ 4^n of P. Erdős, Beweis eines Satzes von Tschebyschef, Acta Sci. Math. (Szeged) 5 (1932), 194-198, as formalised in Mathlib as primorial_le_four_pow.

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes
open scoped ArithmeticFunction.vonMangoldt

theorem TaoFivePrimes.sum_siftedVonMangoldt_le_log_four (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), TaoFivePrimes.siftedVonMangoldt N n ≤ (N : ℝ) * Real.log 4 := by sorry
