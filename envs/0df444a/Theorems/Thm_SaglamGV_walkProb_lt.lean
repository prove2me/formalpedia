-- Prove2me | Theorems.Thm_SaglamGV_walkProb_lt
-- name    : SaglamGV.walkProb_lt
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:35.62258+00:00
-- url     : https://prove2.me/theorems/2f68e91b-ee4a-4671-b2c3-0d688c13f018
-- title:
--   Transition estimate $\Pr[W_\tau=e_{n+1}]<\tau e^{-\tau}/V$, hence $\mathbb E Z<1$
-- statement:
--   Fix $\varepsilon>0$ and $0<\zeta<1$. There are $L$ and $N_0$, depending only on $\varepsilon$ and $\zeta$, such that for all $n\ge N_0$, all $w$ with $L\ln n\le w\le(1/2-\varepsilon)n$ (and $d=w+1$), and every integer $m$ with
--
--   $$
--   \frac{(1-\zeta)R}2\le\tau<(1-\zeta)R,\qquad\tau=V2^{-m},\ R=\ln\frac{2^n}V,
--   $$
--
--   the walk satisfies
--
--   $$
--   \Pr[W_\tau=e_{n+1}]<\frac{\tau e^{-\tau}}V ,
--   $$
--
--   and, for $M$ uniform on $\mathbb F_2^{m\times n}$, the expected number of odd circuits of $B_d$ in $K$ satisfies $\mathbb E Z<1$. Hence some $M$ has no odd circuit in $K$.
--
--   Differences from the source:
--   - encoding: ln n ≪ w and "for all sufficiently large n" → ∃ L, N₀ depending on ε, ζ only, for all n ≥ N₀ and L·ln n ≤ w ≤ (1/2 − ε)n; reason: equivalent to the sequential reading
--   - generalization: the integer m chosen with (1 − ζ)R/2 ≤ τ < (1 − ζ)R → every m ∈ ℕ satisfying that constraint; reason: covers the chosen m; no negative integer m satisfies it (w ≥ 1 gives V ≥ n > n ln 2 ≥ R > τ, so 2^{−m} < 1), so m ∈ ℕ loses no instance
--   - encoding: Pr[W_τ = e_{n+1}] and E over M → walkProb (the law of W_τ) and avgM (the average over all 2^{mn} matrices); reason: same values
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.3 ("It remains to prove Pr[W_τ = e_{n+1}] < τe^{−τ}/V"); §3.3, pp.4–5 (proof; "This proves the desired transition bound, and hence E Z < 1")

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Params
import Definitions.Def_SaglamGV_Circuit
import Definitions.Def_SaglamGV_Walk

namespace SaglamGV

/-- The transition estimate and $E Z < 1$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.3: "It remains to prove
Pr[W_τ = e_{n+1}] < τe^{−τ}/V"; §3.3, p.5: "This proves the desired transition bound, and hence
E Z < 1").

Fix $ε > 0$ and $0 < ζ < 1$. For all large $n$, all $w$ with $\ln n ≪ w ≤ (1/2 − ε)n$ ($d = w+1$)
and every integer $m$ with $(1−ζ)R/2 ≤ τ < (1−ζ)R$, $τ = V2^{−m}$:
$\Pr[W_τ = e_{n+1}] < τe^{−τ}/V$, and $E Z < 1$ for $M$ uniform on $𝔽_2^{m×n}$.

**Formalization Note** "$\ln n ≪ w$" and "for all sufficiently large $n$" are $∃ L, N_0$ depending
on $ε, ζ$ only. Stated for every admissible $m$. -/
theorem walkProb_lt (ε ζ : ℝ) (hε : 0 < ε) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ L : ℝ, ∃ N₀ : ℕ, ∀ n w m : ℕ, N₀ ≤ n → L * Real.log n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      (1 - ζ) * redund n (w + 1) / 2 ≤ tau n (w + 1) m →
      tau n (w + 1) m < (1 - ζ) * redund n (w + 1) →
      walkProb n (w + 1) (tau n (w + 1) m) (eLast n) <
          tau n (w + 1) m * Real.exp (-tau n (w + 1) m) / (vol n (w + 1) : ℝ) ∧
        avgM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) => (oddCircuitCount (w + 1) M : ℝ)) < 1 := by sorry

end SaglamGV
