-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P06_classicalBit_unlimitedSharing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P06.classicalBit_unlimitedSharing
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:04:24.726189+00:00
-- url     : https://prove2.me/theorems/cd2ee565-73da-470c-a5d3-8d713fe6bb20
-- title:
--   A classical bit can be shared among any finite positive number of parties
-- statement:
--   Let $p\in[0,1]$ and let $n\geq1$ be an integer. Give the all-zero string in $\{0,1\}^n$ probability $p$ and the all-one string probability $1-p$, with zero probability elsewhere. Writing this law as $q_{n,p}$, it is nonnegative and normalized, and for every party $i$ and bit $b$,
--
--   $$
--   \sum_{x:x_i=b}q_{n,p}(x)=\begin{cases}p,&b=0,\\1-p,&b=1,\end{cases}
--   \qquad
--   \Pr_{q_{n,p}}[x_i=x_j\text{ for all }i,j]=1.
--   $$
--
--   Thus every party has the prescribed classical bit and all parties agree with certainty, for every finite positive party count. Deterministic bits $p=0$ and $p=1$ are included.
--
--   This is the classical comparison with the non-shareability of coherent EPR entanglement. The parameter $p$ denotes the probability of zero.
-- source:
--   Is Entanglement Monogamous?, arXiv:quant-ph/0307120v1, PDF p. 5, Section II, unnumbered: a classical bit can be shared with arbitrarily many parties

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section II, arXiv:quant-ph/0307120v1, PDF p.5: every Bernoulli bit
can be shared among every finite positive number of parties. The constructed
law is normalized, has the specified marginal at each party, and gives perfect
agreement. Deterministic p=0 and p=1 are included. -/
theorem classicalBit_unlimitedSharing (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ x, 0 ≤ sharedBitLaw n p x) ∧
    (∑ x : Fin n → Bool, sharedBitLaw n p x) = 1 ∧
    (∀ (i : Fin n) (b : Bool),
      (∑ x : Fin n → Bool, if x i = b then sharedBitLaw n p x else 0) =
        if b then 1 - p else p) ∧
    (∑ x : Fin n → Bool,
      if ∀ i j : Fin n, x i = x j then sharedBitLaw n p x else 0) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P06

end
