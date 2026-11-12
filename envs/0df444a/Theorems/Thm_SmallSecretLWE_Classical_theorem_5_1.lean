-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_theorem_5_1
-- name    : SmallSecretLWE.Classical.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:36.779488+00:00
-- url     : https://prove2.me/theorems/fe53495b-fbcc-4712-add5-78294d573f17
-- title:
--   Theorem 5.1 (classical clause, items 1 and 2) — distinguishing planted small-secret bounded-noise k-LIN$(\mathbb Z_q)$ from random in time $\tilde O(m_0(32Bn/\varepsilon)^{l/2})$
-- statement:
--   There are an absolute constant $C>0$, constants $K>0$, $c\in\mathbb N$ and one randomized program $P$ with the following property. Let $n,m,q,k$ be positive integers, $l\in\mathbb N$, $D>0$, $0<B\le q/2$, $\varepsilon\in(0,1/2)$, put $\lambda=\ln(32Bn/\varepsilon)$ and $T_0=\lfloor l\lambda\rfloor$, and let $A\in\mathbb Z_q^{m\times n}$ have exactly $k$ nonzero entries per row. Suppose the conditions of one item hold:
--   - item 1: $\lceil k/2\rceil\le l\le n-\lfloor k/2\rfloor$, $q\ge\frac{16lD}{\varepsilon}\lambda$, $m\ge l\lambda(q-1)^{\lfloor k/2\rfloor}(Cn/l)^{\lceil k/2\rceil}$, and $f=(q-1)^{\lfloor k/2\rfloor}(Cn/l)^{\lceil k/2\rceil}(32Bn/\varepsilon)^{l/2}$;
--   - item 2: $k\le l\le n$, $q\ge\frac{16lD}{\varepsilon}\lambda$, $m\ge l\lambda(Cn/l)^{k}$, and $f=(Cn/l)^{k}(32Bn/\varepsilon)^{l/2}$.
--
--   Then $P$, run on $(A,b)$ with $B,D,\varepsilon$ given through the parameter oracle,
--   1. halts on every input $b\in\mathbb Z_q^m$ and every run within cost $K f\,(\ln(2+f+q+n+m+1/\varepsilon))^{c}$;
--   2. for every $\varepsilon'>0$ and every law $\Psi$ on $\mathbb Z_q$ with $\Pr_{\tilde e\sim\Psi^{T_0}}[\|\tilde e\|_\infty>D]<\varepsilon'$:
--   $$\Pr_{b\sim\mathrm{Unif}(\mathbb Z_q^m)}[P \text{ outputs RANDOM}]\ge1-(2.5\varepsilon+\varepsilon'),$$
--   and for every $s\in\mathbb Z_q^n$ with $\|s\|_\infty\le B$,
--   $$\Pr_{e\sim\Psi^m}[P(A,As+e)\text{ outputs PLANTED}]\ge1-(2.5\varepsilon+\varepsilon').$$
--
--   This is the formal version of the headline Theorem 1.1: sparse LWE with secrets of size $B$ and bounded noise is distinguished in time roughly $m_0(Bn/\varepsilon)^{l/2}$, where $m_0$ is the number of samples the item requires.
--
--   **Formalization Note.** The secret bound $\|s\|_\infty\le B$ uses centered values. $\varepsilon'$ and $\Psi$ are universally quantified with the noise hypothesis, so no choice of them can be used to satisfy the statement; the random-case clause excludes a program that always answers PLANTED.
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: 'There exists a classical (resp. quantum) algorithm …' → the classical clause only; reason: the quantum clause needs a quantum RAM model and is not part of this mission (mission description, Formalization scope)
--   - reading: $\log$ → natural logarithm `Real.log`; reason: Theorem 1.1 writes $\ln$; with $\ln$ the thresholds on $q$ and $m$ are smallest, the stronger reading
--   - reading: $T=l\log(32Bn/\varepsilon)$ as the length of $\Psi^T$ → $T_0=\lfloor l\ln(32Bn/\varepsilon)\rfloor_+$ (`Nat.floor`, $0$ when negative); reason: $T$ need not be an integer; $\Pr_{\Psi^t}[\|\tilde e\|_\infty>D]$ is nondecreasing in $t$, so the floor is the weakest integer hypothesis and gives the strongest theorem
--   - reading: 'the algorithm takes time $\tilde O(f)$' → every run on every input halts within log-cost $Kf(\ln(2+f+q+n+m+1/\varepsilon))^c$; reason: worst case; the slack polylog in $f,q,n,m,1/\varepsilon$ is the paper's $\tilde O$ convention (Lemma 4.1, Corollary 4.8 fn. 9)
--   - reading: 'there exists … algorithm … where $C>0$ is an absolute constant' → $\exists C,K,c,P$ before all of $n,m,q,k,l,D,B,\varepsilon,A$; reason: one uniform algorithm; a parameter-dependent one would trivialize the time bound
--   - encoding: 'algorithm', instance $I$, its parameters → one program on the fair-coin log-cost RAM; input `instanceInput k l A b`; $B,D,\varepsilon$ behind `paramOracle [B, D, ε]`; $\Psi,\varepsilon',s$ unseen; reason: the paper names no machine
--   - encoding: 'distinguish … with failure probability at most $2.5\varepsilon+\varepsilon'$' → both cases separately: $\Pr[\text{output }[0]]\ge1-(2.5\varepsilon+\varepsilon')$ on random $b$, $\Pr[\text{output }[1]]\ge1-(2.5\varepsilon+\varepsilon')$ on planted $b$; any other output is a failure; reason: the standard meaning of a distinguisher's failure probability
--   - encoding: $\lceil k/2\rceil$, $\lfloor k/2\rfloor$, $l\le n-\lfloor k/2\rfloor$, $(32Bn/\varepsilon)^{l/2}$ → `(k + 1) / 2`, `k / 2`, `l + k / 2 ≤ n`, `Real.rpow`; reason: same numbers
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), pp. 32–33, Theorem 5.1 (classical clause, items 1 and 2)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_SmallSecretLWE_Classical_Basic
import Definitions.Def_SmallSecretLWE_Classical_Encoding

open PrefixMixLearn.Proper (Program HaltsWithin)

namespace SmallSecretLWE.Classical

/-- Theorem 5.1, classical clause, items 1 and 2. There are an absolute constant `C > 0`,
constants `K > 0`, `c ∈ ℕ` and one fair-coin log-cost program `P` such that for all positive
integers `n, m, q, k`, every `l ∈ ℕ`, all reals `D > 0`, `0 < B ≤ q/2`, `ε ∈ (0, 1/2)`, with
`T₀ = ⌊l ln(32Bn/ε)⌋`, and every `A ∈ Z_q^{m×n}` with exactly `k` nonzero entries per row: if the
conditions of item 1 (`⌈k/2⌉ ≤ l ≤ n − ⌊k/2⌋`, `q ≥ (16lD/ε) ln(32Bn/ε)`,
`m ≥ l ln(32Bn/ε) (q−1)^{⌊k/2⌋} (Cn/l)^{⌈k/2⌉}`, `f = (q−1)^{⌊k/2⌋} (Cn/l)^{⌈k/2⌉}
(32Bn/ε)^{l/2}`) or of item 2 (`k ≤ l ≤ n`, the same `q`-condition,
`m ≥ l ln(32Bn/ε) (Cn/l)^k`, `f = (Cn/l)^k (32Bn/ε)^{l/2}`) hold, then, run on `(A, b)` with
`B, D, ε` behind the parameter oracle:
* on every input `b` every run halts within log-cost `K f (ln(2 + f + q + n + m + 1/ε))^c`;
* for every `ε' > 0` and every noise law `Ψ` on `Z_q` with `Pr_{ẽ∼Ψ^{T₀}}[‖ẽ‖_∞ > D] < ε'`:
  on a random instance it outputs RANDOM (`[0]`) with probability at least `1 − (2.5ε + ε')`,
  and for every secret `s` with `‖s‖_∞ ≤ B`, on the planted instance `b = As + e`, `e ∼ Ψ^m`, it
  outputs PLANTED (`[1]`) with probability at least `1 − (2.5ε + ε')`. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∃ c : ℕ, ∃ P : Program,
      ∀ (n m q k : ℕ) [NeZero q], 0 < n → 0 < m → 0 < k →
      ∀ (l : ℕ) (D B ε : ℝ), 0 < D → 0 < B → B ≤ (q : ℝ) / 2 → 0 < ε → ε < 1 / 2 →
      ∀ A : Matrix (Fin m) (Fin n) (ZMod q), HasKSparseRows k A →
      ∀ f : ℝ,
        (((k + 1) / 2 ≤ l ∧ l + k / 2 ≤ n ∧
            16 * l * D / ε * Real.log (32 * B * n / ε) ≤ (q : ℝ) ∧
            l * Real.log (32 * B * n / ε) * ((q : ℝ) - 1) ^ (k / 2) *
              (C * n / l) ^ ((k + 1) / 2) ≤ (m : ℝ) ∧
            f = ((q : ℝ) - 1) ^ (k / 2) * (C * n / l) ^ ((k + 1) / 2) *
              (32 * B * n / ε) ^ ((l : ℝ) / 2)) ∨
         (k ≤ l ∧ l ≤ n ∧
            16 * l * D / ε * Real.log (32 * B * n / ε) ≤ (q : ℝ) ∧
            l * Real.log (32 * B * n / ε) * (C * n / l) ^ k ≤ (m : ℝ) ∧
            f = (C * n / l) ^ k * (32 * B * n / ε) ^ ((l : ℝ) / 2))) →
        (∀ b : Fin m → ZMod q,
          HaltsWithin P (paramOracle [B, D, ε]) (instanceInput k l A b)
            (K * f * Real.log (2 + f + q + n + m + 1 / ε) ^ c)) ∧
        ∀ ε' : ℝ, 0 < ε' → ∀ Ψ : PMF (ZMod q),
          tailProb Ψ ⌊(l : ℝ) * Real.log (32 * B * n / ε)⌋₊ D < ε' →
            1 - (2.5 * ε + ε') ≤ randomAccept P (paramOracle [B, D, ε]) k l A ∧
            ∀ s : Fin n → ZMod q, linf s ≤ B →
              1 - (2.5 * ε + ε') ≤ plantedAccept P (paramOracle [B, D, ε]) k l A s Ψ := by sorry

end SmallSecretLWE.Classical
