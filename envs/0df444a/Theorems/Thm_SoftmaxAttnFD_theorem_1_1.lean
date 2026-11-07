-- Prove2me | Theorems.Thm_SoftmaxAttnFD_theorem_1_1
-- name    : SoftmaxAttnFD.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:23.636762+00:00
-- url     : https://prove2.me/theorems/e5c6f239-49f0-4f47-8f63-6c46bd18469b
-- title:
--   Theorem 1.1, p.2 — softmax attention in expected time $\tilde O((mn)^{k/(k+1)}+m+n)$, $k=\lfloor d/2\rfloor$
-- statement:
--   Fix integers $d\ge1$ and $r\ge1$, and let $k=\lfloor d/2\rfloor$. There are a program of the logarithmic-cost RAM with fair coins and constants $C>0$ and $K$ such that for all $m,n\ge1$, $p\ge0$, and all rational $Q\in\mathbb Q^{m\times d}$, $K_e\in\mathbb Q^{n\times d}$, $V\in\mathbb Q^{n\times r}$ with entries of magnitude at most $B\ge1$ and encoding length at most $b$:
--
--   1. on every coin tape on which the run halts, the output $\hat O$ satisfies $\|\hat O-\mathrm{Att}(Q,K_e,V)\|_{\max}\le2^{-p}$;
--   2. the expected bit cost is at most
--   $$C\,\bigl((mn)^{k/(k+1)}+m+n\bigr)\,\bigl(b+\log_2(m+n)+\log_2B+p\bigr)^K.$$
--
--   This matches the best known bound for batch maximum inner product in each fixed dimension and improves the previous bound $\tilde O(n^{2-1/d})$. Since the dependence on $B$ and $1/\varepsilon$ is polylogarithmic, a positive rational inverse temperature $\beta$ is absorbed by replacing $Q$ with $\beta Q$.
--
--   **Formalization Note** The cost is $+\infty$ on a tape on which the run does not halt, so the cost bound forces halting with probability one.
--
--   Differences from the source:
--   - encoding: "Las Vegas algorithm", "expected running time", measured in "bit operations" → a finite program of the logarithmic-cost RAM with fair coins; correct on every halting tape; expected cost in ℝ≥0∞ with cost ⊤ off halting; reason: the page names no machine; this keeps its bit count and random access (Machine)
--   - encoding: soft-O suppressing poly_d(b, log(m + n), log B, log(1/ε)), constants depending on d, r → C·(·)·(b + log₂(m+n) + log₂B + p)^K with P, C, K chosen after d, r and before the instance; 1 ≤ m, n; reason: log₂(1/ε) = p; the base is at least 1, so its powers dominate all such polynomials; F_d is defined for m, n ≥ 1
--   - encoding: Rational input and output matrices → encoded triples at fixed addresses; B, b bounds under ∀ and not inputs; unreduced triples allowed; reason: covers every encoding the page allows ("signed numerators and positive denominators")
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Theorem 1.1, p.2; Definition 2.1, p.10; (2.1), p.11

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_SoftmaxAttnFD_F
import Definitions.Def_SoftmaxAttnFD_Attention

namespace SoftmaxAttnFD

/-- **Theorem 1.1** (Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension,
arXiv:2611.06055, sha256 a60f7609…, p.2). For fixed `d, r ≥ 1` there is a Las Vegas algorithm for
Attention_d with `r` value channels whose expected running time is
`Õ((mn)^{k/(k+1)} + m + n)`, `k = ⌊d/2⌋`, where soft-O hides `poly_d(b, log(m+n), log B, log(1/ε))`.

**Formalization Note** The algorithm is a finite program of the logarithmic-cost RAM with fair coins
(`TimeSpaceMA.Program`, reused), chosen with `C` and `K` after `d, r` and before the instance. `ε = 2^{−p}`, so
`log₂(1/ε) = p`; the base of the power is at least 1, so it dominates every polynomial in the four
parameters. `B` and `b` are bounds, not inputs: the bound holds for every valid choice. Correctness
holds on every halting tape, and `cost` is `⊤` on a non-halting tape. -/
theorem theorem_1_1 (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (m n p : ℕ), 1 ≤ m → 1 ≤ n →
        ∀ (Q : Fin m → Fin d → RatEnc) (Kₑ : Fin n → Fin d → RatEnc) (V : Fin n → Fin r → RatEnc)
          (B : ℝ) (b : ℕ), 1 ≤ B → MatBounded Q B b → MatBounded Kₑ B b → MatBounded V B b →
          LasVegasWithin P (attnMem p Q Kₑ V) (attnGood p Q Kₑ V)
            (C * F d m n * ((b : ℝ) + Real.logb 2 ((m : ℝ) + n) + Real.logb 2 B + p) ^ K) := by sorry

end SoftmaxAttnFD
