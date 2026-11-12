-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_corollary_4_8
-- name    : SmallSecretLWE.Classical.corollary_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:28.254623+00:00
-- url     : https://prove2.me/theorems/47b3a7bf-8ad9-40bd-9f28-14e9415179a8
-- title:
--   Corollary 4.8 (both items) — classical relaxed SIS for sparse $A$: $c$ with $c_i=\pm1$, $\|A^Tc\|_1\le R$, short, in time $\tilde O(m_0\sqrt{N/\binom{\lfloor R/4\rfloor+l}{l}})$
-- statement:
--   There is an absolute constant $C>0$ such that for every fixed $\alpha\in(0,1)$ there are one randomized program $P$ and constants $K>0$, $c$ with the following property. Let $k,n,l,q$ be positive integers, $m\in\mathbb N$, $R\ge0$, $\delta\in(0,1/2)$, and let $A\in\mathbb Z_q^{m\times n}$ have exactly $k$ nonzero entries per row. Put $N=\binom nl(q-1)^l$, $\Lambda=l\ln\frac{qn}{R/4+l}$ and
--   - item 1: $\lceil k/2\rceil\le l\le n-\lfloor k/2\rfloor$, $m\ge\frac1\alpha\Lambda(q-1)^{\lfloor k/2\rfloor}(Cn/l)^{\lceil k/2\rceil}$, and $f=(q-1)^{\lfloor k/2\rfloor}(Cn/l)^{\lceil k/2\rceil}\sqrt{N/\binom{\lfloor R/4\rfloor+l}{l}}$;
--   - item 2: $k\le l\le n$, $m\ge\frac1\alpha\Lambda(Cn/l)^{k}$, and $f=(Cn/l)^{k}\sqrt{N/\binom{\lfloor R/4\rfloor+l}{l}}$.
--
--   If the conditions of either item hold, then $P$, run on $A$ with $R,\delta$ given through the parameter oracle, halts on every run within cost $K f(\ln(2+f+q+n+m+1/\delta))^c$, and with probability at least $1-2\delta$ outputs $c\in\mathbb Z_q^m$ with
--   $$\|c\|_1\le\frac{4}{\ln(1/\alpha)}\Big(\Lambda+\ln\frac1\delta+\ln\ln\frac1\delta+12\Big),\qquad c_i\in\{\pm1\}\text{ for some }i,\qquad\|A^Tc\|_1\le R .$$
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: $\log$ → natural logarithm `Real.log` throughout; reason: Corollary 4.7, whose $T$ and $J$ this bound comes from, writes $\ln$; Theorem 1.1 writes $\ln$
--   - reading: 'Let $\alpha\in(0,1)$ be a fixed parameter … where $C>0$ is an absolute constant' → $\exists C>0,\ \forall\alpha\in(0,1),\ \exists P,K,c$; reason: $C$ is absolute; the algorithm and the $\tilde O$ constants may depend on the fixed $\alpha$
--   - reading: 'runs in time $\tilde O(f)$', $\tilde O$ also hiding $\log(1/\delta)$ and lower terms (fn. 9) → on every input every run halts within log-cost $Kf(\ln(2+f+q+n+m+1/\delta))^c$; reason: worst case on every run; the slack is the paper's $\tilde O$ convention (polylog of $f$, $q$, $n$, $m$, $1/\delta$)
--   - encoding: 'an algorithm' given $A$, $R$, $\delta$; output $c$ → one program on the fair-coin log-cost RAM, input `matrixInput k l A`, $R,\delta$ behind `paramOracle [R, δ]`, output `vecCells c`; reason: the paper names no machine
--   - encoding: 'finds $c$ … except with probability $2\delta$' → $\Pr[\text{output is such a }c]\ge1-2\delta$; reason: same event
--   - encoding: $\lceil k/2\rceil$, $\lfloor k/2\rfloor$, $l\le n-\lfloor k/2\rfloor$ → `(k + 1) / 2`, `k / 2`, `l + k / 2 ≤ n` in ℕ; reason: same integers
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), pp. 22–23, Corollary 4.8 (fn. 9)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_SmallSecretLWE_Classical_Basic
import Definitions.Def_SmallSecretLWE_Classical_Encoding

open PrefixMixLearn.Proper (Program HaltsWithin outProb)

namespace SmallSecretLWE.Classical

/-- Corollary 4.8 (both items). There is an absolute constant `C > 0` such that for every fixed
`α ∈ (0, 1)` there are one fair-coin log-cost program `P` (given `R, δ` through the parameter
oracle) and constants `K > 0`, `c` with the following property. For all positive integers
`k, n, l, q`, every `m`, all reals `R ≥ 0`, `δ ∈ (0, 1/2)` and every `A ∈ Z_q^{m×n}` with
exactly `k` nonzero entries per row, if the conditions of item 1
(`⌈k/2⌉ ≤ l ≤ n − ⌊k/2⌋`, `m ≥ (1/α) l ln(qn/(R/4+l)) (q−1)^{⌊k/2⌋} (Cn/l)^{⌈k/2⌉}`, and
`f = (q−1)^{⌊k/2⌋} (Cn/l)^{⌈k/2⌉} √(binom(n,l)(q−1)^l / binom(⌊R/4⌋+l, l))`) or of item 2
(`k ≤ l ≤ n`, `m ≥ (1/α) l ln(qn/(R/4+l)) (Cn/l)^k`, and
`f = (Cn/l)^k √(binom(n,l)(q−1)^l / binom(⌊R/4⌋+l, l))`) hold, then every run of `P` on `A`
halts within log-cost `K f (ln(2 + f + q + n + m + 1/δ))^c`, and with probability at least
`1 − 2δ` it outputs `c ∈ Z_q^m` with
`‖c‖_1 ≤ (4/ln(1/α))(l ln(qn/(R/4+l)) + ln(1/δ) + ln ln(1/δ) + 12)`, `c_i ∈ {±1}` for some
`i`, and `‖A^T c‖_1 ≤ R`. -/
theorem corollary_4_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 →
    ∃ (P : Program) (K : ℝ) (c : ℕ), 0 < K ∧
      ∀ (k n l q m : ℕ) [NeZero q], 0 < k → 0 < n → 0 < l →
      ∀ (R δ : ℝ), 0 ≤ R → 0 < δ → δ < 1 / 2 →
      ∀ A : Matrix (Fin m) (Fin n) (ZMod q), HasKSparseRows k A →
      ∀ f : ℝ,
        (((k + 1) / 2 ≤ l ∧ l + k / 2 ≤ n ∧
            1 / α * ((l : ℝ) * Real.log ((q : ℝ) * n / (R / 4 + l))) *
              ((q : ℝ) - 1) ^ (k / 2) * (C * n / l) ^ ((k + 1) / 2) ≤ (m : ℝ) ∧
            f = ((q : ℝ) - 1) ^ (k / 2) * (C * n / l) ^ ((k + 1) / 2) *
              Real.sqrt ((n.choose l : ℝ) * ((q : ℝ) - 1) ^ l /
                ((⌊R / 4⌋₊ + l).choose l : ℝ))) ∨
         (k ≤ l ∧ l ≤ n ∧
            1 / α * ((l : ℝ) * Real.log ((q : ℝ) * n / (R / 4 + l))) * (C * n / l) ^ k ≤
              (m : ℝ) ∧
            f = (C * n / l) ^ k *
              Real.sqrt ((n.choose l : ℝ) * ((q : ℝ) - 1) ^ l /
                ((⌊R / 4⌋₊ + l).choose l : ℝ)))) →
        HaltsWithin P (paramOracle [R, δ]) (matrixInput k l A)
            (K * f * Real.log (2 + f + q + n + m + 1 / δ) ^ c) ∧
          1 - 2 * δ ≤ outProb P (paramOracle [R, δ]) (matrixInput k l A) (fun o =>
            ∃ cv : Fin m → ZMod q, o = vecCells cv ∧
              l1 cv ≤ 4 / Real.log (1 / α) *
                ((l : ℝ) * Real.log ((q : ℝ) * n / (R / 4 + l)) + Real.log (1 / δ) +
                  Real.log (Real.log (1 / δ)) + 12) ∧
              (∃ i, cv i = 1 ∨ cv i = -1) ∧
              l1 (A.transpose.mulVec cv) ≤ R) := by sorry

end SmallSecretLWE.Classical
