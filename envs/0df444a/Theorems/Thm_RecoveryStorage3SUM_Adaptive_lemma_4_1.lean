-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_1
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:10.497963+00:00
-- url     : https://prove2.me/theorems/e081a93c-a833-4ab8-9778-166b5da204a9
-- title:
--   Lemma 4.1 — the sample $R$ marks every heavy value
-- statement:
--   Let $A,B$ be sets of $n$ integers and $0\le\delta<1$. Draw $R\subseteq A$ uniformly among subsets of size $\min(\lceil3n^{1-\delta}\rceil,n)$, and let $C^\star=R+B$. For every $d>0$ and all large $n$,
--   $$\Pr_R\big[\text{some }c\in A+B\text{ with }\mathrm{count}(c)\ge n^\delta\log^2 n\text{ has }c\notin C^\star\big]\le n^{-d}.$$
--
--   This is the first event of the preprocessing. It lets the analysis treat every unmarked value as light, while only $R$ needs to be stored.
--
--   Differences from the source:
--   - generalization: the polynomial bound on input integers in Section 2 → arbitrary finite integer sets A and B of equal cardinality; reason: coverage depends only on pair multiplicities and uniform subset sampling; every source input is included
--   - reading: "with high probability" → for every fixed exponent $d>0$, failure at most $n^{-d}$ for $n\ge n_0$; reason: pp.10-13 give tunable polynomial tails
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.1, p.10

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Lemma 4.1, p.10: with high probability over the uniform sample `R`, every heavy value is marked. -/
theorem lemma_4_1 (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (d : ℝ) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ A B : Finset ℤ, n₀ ≤ A.card → B.card = A.card →
      unifProb (sampleSpace A δ) (fun R => ¬ HeavyCovered A B R δ) ≤ (A.card : ℝ) ^ (-d) := by sorry

end RecoveryStorage3SUM.Adaptive
