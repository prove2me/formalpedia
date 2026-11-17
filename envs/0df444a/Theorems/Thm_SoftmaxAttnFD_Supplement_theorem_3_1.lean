-- Prove2me | Theorems.Thm_SoftmaxAttnFD_Supplement_theorem_3_1
-- name    : SoftmaxAttnFD.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:42:33.595677+00:00
-- url     : https://prove2.me/theorems/8a66e5e3-8782-4ec0-95db-cf28ec2ffd59
-- title:
--   Theorem 3.1, p.13 — $\mathrm{BatchMaxIP}_d$ reduces to one attention call in the same dimension ($Q=\beta_0X$, $K=Y$) with deterministic additional time $\tilde O((m+n)d)$
-- statement:
--   Let $X\in\mathbb Z^{m\times d}$ and $Y\in\mathbb Z^{n\times d}$ have coordinate magnitudes at most an integer $B\ge1$, and set $C=8$, $\beta_0=C\lceil\log_2(n+1)\rceil$, $\varepsilon_0=2^{-\lceil\log_2(CdB)\rceil}$. Set $Q=\beta_0X$ and $K=Y$. Each of the following attention reductions solves $\mathrm{BatchMaxIP}_d$ (computes every $M_i=\max_j x_i\cdot y_j$ exactly) with the same $m,n,d$ and deterministic additional time $\tilde O((m+n)d)$:
--
--   1. one call with $V=Y$, $r=d$ value channels, magnitude bound $\beta_0B$, and error tolerance $\varepsilon_0$;
--   2. one call with $V=dB\,Y$, $r=d$ value channels, magnitude bound $\max\{\beta_0B,dB^2\}$, and constant error tolerance $\varepsilon_c=1/4$;
--   3. for either value matrix $V$, $d$ calls with one value channel each, using its columns separately and the same error tolerance.
--
--   Precisely: there are absolute constants $C'>0$ and $K$ (independent of $d$) such that the instances obey the stated magnitude bounds (with encoding length that of the bound), and for each of the four variants there are coin-free pre- and post-processing programs satisfying the reduction contract of `MaxIPReduction`: the pre-processing writes the attention input(s) within bit cost
--
--   $$C'\,(m+n)\,d\,\bigl(\log_2(m+n)+\log_2(d+1)+\log_2(B+1)\bigr)^K,$$
--
--   and for every attention output within the tolerance, with output cells of bit length at most $L$, the post-processing returns the exact $M_i$ within the same bound with $L$ added to the base.
--
--   The reduction transfers lower bounds for exact maximum inner product to attention in the same dimension, at inverse-polynomial and at constant error; it is why the goal's exponent matches the best known maximum-inner-product bounds.
--
--   **Formalization Note** "The dimension may grow in this section, and soft-O suppresses only logarithmic factors in $m+n,d,B$" (p.13): $C'$ and $K$ are chosen first, and the programs before $d$ and the instance.
--
--   Differences from the source:
--   - encoding: "deterministic additional time Õ((m + n)d)", soft-O suppressing logarithmic factors in m + n, d, B → coin-free pre- and post-processing programs of the logarithmic-cost RAM; bit cost C(m+n)d·λ^K with λ = log₂(m+n) + log₂(d+1) + log₂(B+1), C, K absolute; the attention calls are not charged; 1 ≤ n, 1 ≤ d; reason: the page names no machine (base Machine); λ^K dominates every polylog in m + n, d, B; ε₀ = 2^{−⌈log₂(CdB)⌉} is undefined at d = 0 and max_{j∈[n]} at n = 0
--   - generalization: post-processing of the paper's dyadic outputs, of logarithmic encoding length in m + n, d, B → post-processing correct for every output within the tolerance, at bit cost C(m+n)d(λ + L)^K, L the bit length of the output cells read; reason: on the paper's dyadic outputs L = O(λ), which gives the paper's Õ((m + n)d)
--   - generalization: "magnitude bound β₀B", "max{β₀B, dB²}" → the produced matrices have entries of magnitude at most the bound and encoding length at most Nat.size of the bound; reason: the proof states that the inputs have logarithmic encoding length; the magnitude clause is unchanged
--   - generalization: m a positive integer (rows x_i, i ∈ [m], [m] defined for positive integers, p.9) → every m : ℕ, including m = 0; reason: at m = 0 there is nothing to compute and every reduction contract holds trivially; on m ≥ 1 the statement is the paper's
--   - encoding: "one call", "d calls", "solves BatchMaxIP_d" → input cells m, n, d, B, X, Y (integer triples); pre-processing writes the attention input after its own input (in (c): the shared m, n, p, Q, K once, then the d value columns); post-processing reads the input followed by the attention output cells and writes the triples of M_i; reason: the page names no format; in (c) writing Q and K once is how the proof counts O((m + n)d) coordinate operations
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Theorem 3.1 and §3.1, p.13 (PDF p.16); informal form Theorem 1.2, p.3 (PDF p.6); Definition 2.2, p.10

import Definitions.Def_SoftmaxAttnFD_Supplement_MaxIPReduction

namespace SoftmaxAttnFD

namespace Supplement

/-- **Theorem 3.1** (Dimension-preserving reduction; Huang, Chen, Softmax Attention with Any
Temperature in Fixed Dimension, arXiv:2611.06055, sha256 a60f7609…, p.13; informal form Theorem 1.2,
p.3). Set `Q = β₀X` and `K = Y`. Each of the attention reductions below solves BatchMaxIP_d with the
same `m, n, d` and deterministic additional time `Õ((m + n)d)`.
(a) One call with `V = Y`, `r = d` value channels, magnitude bound `β₀B`, and error tolerance `ε₀`.
(b) One call with `V = dB Y`, `r = d` value channels, magnitude bound `max{β₀B, dB²}`, and constant
error tolerance `ε_c = 1/4`.
(c) For either value matrix `V`, `d` calls with one value channel each, using its columns separately
and the same error tolerance.

Here `C = 8`, `β₀ = C⌈log₂(n + 1)⌉`, `ε₀ = 2^{−⌈log₂(CdB)⌉}` (§3.1, p.13).

**Formalization Note** The dimension is not fixed ("The dimension may grow in this section, and
soft-O suppresses only logarithmic factors in `m + n, d, B`"): the constants `C`, `K` come first and
do not depend on `d`; the programs are chosen after `C`, `K` and before `d` and the instance. The
magnitude bounds are stated for the produced matrices, together with the encoding length
`Nat.size` of the bound. -/
theorem theorem_3_1 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      -- magnitude bounds of the instances of (a) and (b)
      (∀ (m n d B : ℕ) (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ),
        1 ≤ n → 1 ≤ d → 1 ≤ B → IntBounded X B → IntBounded Y B →
        (MatBounded (redQ n X) ((beta0 n * B : ℕ) : ℝ) (beta0 n * B).size ∧
          MatBounded (intMat Y) ((beta0 n * B : ℕ) : ℝ) (beta0 n * B).size ∧
          MatBounded (intMat (valA n d B Y)) ((beta0 n * B : ℕ) : ℝ) (beta0 n * B).size) ∧
        (MatBounded (redQ n X) ((max (beta0 n * B) (d * B ^ 2) : ℕ) : ℝ)
            (max (beta0 n * B) (d * B ^ 2)).size ∧
          MatBounded (intMat Y) ((max (beta0 n * B) (d * B ^ 2) : ℕ) : ℝ)
            (max (beta0 n * B) (d * B ^ 2)).size ∧
          MatBounded (intMat (valB n d B Y)) ((max (beta0 n * B) (d * B ^ 2) : ℕ) : ℝ)
            (max (beta0 n * B) (d * B ^ 2)).size)) ∧
      -- (a) one call, V = Y, r = d, ε₀ = 2^{-⌈log₂(8dB)⌉}
      (∃ Pre Post : TimeSpaceMA.Program, OneCallReduction Pre Post C K pA valA) ∧
      -- (b) one call, V = dB·Y, r = d, ε_c = 1/4
      (∃ Pre Post : TimeSpaceMA.Program, OneCallReduction Pre Post C K (fun _ _ => pB) valB) ∧
      -- (c) d single-channel calls, for either value matrix, same tolerance
      (∃ Pre Post : TimeSpaceMA.Program, ScalarCallsReduction Pre Post C K pA valA) ∧
      (∃ Pre Post : TimeSpaceMA.Program,
        ScalarCallsReduction Pre Post C K (fun _ _ => pB) valB) := by sorry

end Supplement

end SoftmaxAttnFD
