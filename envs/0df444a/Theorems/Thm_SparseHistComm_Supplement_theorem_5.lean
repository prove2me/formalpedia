-- Prove2me | Theorems.Thm_SparseHistComm_Supplement_theorem_5
-- name    : SparseHistComm.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:45:30.53622+00:00
-- url     : https://prove2.me/theorems/df7217a8-3df5-4fae-b7f0-fb947360cf82
-- title:
--   Theorem 5 — small and large costs of homogeneity
-- statement:
--   The theorem records all three regimes of the communication cost of homogeneity.
--
--   1. For fixed admissible $n,k,D,\delta$, as $d\to\infty$,
--      $$
--      \frac{C_{\mathrm{hom}}(D,\delta)}{C_{\mathrm{het}}(D,\delta)}
--      \longrightarrow
--      \frac{\Lambda_{n,k,D}(\delta)}{(1-\delta)(nk-\lfloor nD\rfloor)}.
--      $$
--   2. Fix $0<\delta<1$ and let admissible $n,k,D,d$ vary. If $nk-\lfloor nD\rfloor\to\infty$ and
--      $$
--      \frac{nk\log_2(2nk)+1+n\log_2(e(k\lceil\log_2d\rceil+1))}
--      {(nk-\lfloor nD\rfloor)\log_2d}\to0,
--      $$
--      then both $C_{\mathrm{hom}}$ and $C_{\mathrm{het}}$ are asymptotic to $(1-\delta)(nk-\lfloor nD\rfloor)\log_2d$.
--   3. If $k-1/n\le D<k$, then for fixed $n,k,D,\delta$,
--      $$
--      \frac{C_{\mathrm{hom}}(D,\delta)}{C_{\mathrm{het}}(D,\delta)}
--      \longrightarrow \frac{n(1-\delta^{1/n})}{1-\delta},
--      $$
--      and this last expression tends to $n$ as $\delta\downarrow0$.
--
--   Differences from the source:
--   - reading: the unindexed limits in (24), following a sentence that first discusses fixed parameters → arbitrary admissible sequences $(n_s,k_s,D_s,d_s)$ with fixed $0<\delta<1$ satisfying the two displayed limit hypotheses; reason: the proof on pp.19–20 explicitly fixes only $\delta$ in this regime, while fixed $n,k,D$ would make the first hypothesis impossible
--   - encoding: ratios of possibly extended communication infima → eventual finiteness, and eventual nonzero heterogeneous cost where it is a denominator, followed by ratios of `toReal`; reason: this excludes default extended-real conversions without changing any eventual source instance
--   - encoding: $d\to\infty$, growing-parameter asymptotics, and $\delta\downarrow0$ → filter limits over natural dimensions, arbitrary natural-indexed admissible sequences, and the right-neighborhood filter at zero; reason: these are the literal Lean forms of the three printed limits
--   - encoding: $\delta^{1/n}$ → real exponentiation by $1/n$; reason: this is the nonnegative real $n$-th root used in (26)
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 5, p.10, (23)–(26); proof pp.19–20

import Mathlib
import Definitions.Def_SparseHistComm_Chom
import Definitions.Def_SparseHistComm_Lambda
import Definitions.Def_SparseHistComm_threshold
import Definitions.Def_SparseHistComm_Supplement_Chet

open Filter Topology

namespace SparseHistComm

namespace Supplement

/-- **Theorem 5 (Small and large costs of homogeneity)** (Ye–Fan, *Optimal Communication for
Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256
29df82a4…f27c6f), p.10, (23)–(26), proof pp.19–20). All three regimes and the final
`δ ↓ 0` limit are included.

**Formalization Note** Fixed-parameter statements are limits over the natural dimension `d`.
The growing-cost clause follows the proof-pinned sequential reading: `δ` is fixed in `(0,1)`, while
`n,k,D,d` vary through admissible instances. Eventual finiteness and a nonzero heterogeneous cost
are recorded before taking `ENNReal.toReal` ratios. `Real.rpow` is the real `n`-th root. -/
theorem theorem_5 :
    (∀ (n k : ℕ) (D δ : ℝ),
      1 ≤ n → 1 ≤ k → 0 ≤ D → D < k → 0 ≤ δ → δ < 1 →
      (∀ᶠ d in atTop, Chom n k d D δ ≠ ⊤ ∧ Supplement.Chet n k d D δ ≠ ⊤ ∧
        Supplement.Chet n k d D δ ≠ 0) ∧
      Tendsto (fun d : ℕ => (Chom n k d D δ).toReal /
        (Supplement.Chet n k d D δ).toReal) atTop
        (𝓝 (Lambda n k D δ / ((1 - δ) * (threshold n k D : ℝ))))) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ (n k d : ℕ → ℕ) (D : ℕ → ℝ),
        (∀ s, 1 ≤ n s ∧ 1 ≤ k s ∧ 2 ≤ d s ∧ k s ≤ d s ∧
          0 ≤ D s ∧ D s < k s) →
        Tendsto (fun s => threshold (n s) (k s) (D s)) atTop atTop →
        Tendsto (fun s =>
          ((n s * k s : ℕ) * Real.logb 2 (2 * n s * k s) + 1 +
            (n s : ℝ) * Real.logb 2
              (Real.exp 1 * (k s * Nat.clog 2 (d s) + 1))) /
          ((1 : ℝ) * (threshold (n s) (k s) (D s) : ℝ) * Real.logb 2 (d s)))
          atTop (𝓝 0) →
        (∀ᶠ s in atTop, Chom (n s) (k s) (d s) (D s) δ ≠ ⊤ ∧
          Supplement.Chet (n s) (k s) (d s) (D s) δ ≠ ⊤) ∧
        Tendsto (fun s => (Chom (n s) (k s) (d s) (D s) δ).toReal /
          ((1 - δ) * (threshold (n s) (k s) (D s) : ℝ) * Real.logb 2 (d s)))
          atTop (𝓝 1) ∧
        Tendsto (fun s => (Supplement.Chet (n s) (k s) (d s) (D s) δ).toReal /
          ((1 - δ) * (threshold (n s) (k s) (D s) : ℝ) * Real.logb 2 (d s)))
          atTop (𝓝 1)) ∧
    (∀ (n k : ℕ) (D δ : ℝ),
      1 ≤ n → 1 ≤ k → k - 1 / (n : ℝ) ≤ D → D < k → 0 ≤ δ → δ < 1 →
      (∀ᶠ d in atTop, Chom n k d D δ ≠ ⊤ ∧ Supplement.Chet n k d D δ ≠ ⊤ ∧
        Supplement.Chet n k d D δ ≠ 0) ∧
      Tendsto (fun d : ℕ => (Chom n k d D δ).toReal /
        (Supplement.Chet n k d D δ).toReal) atTop
        (𝓝 ((n : ℝ) * (1 - δ ^ (1 / (n : ℝ))) / (1 - δ)))) ∧
    (∀ n : ℕ, 1 ≤ n →
      Tendsto (fun δ : ℝ => (n : ℝ) * (1 - δ ^ (1 / (n : ℝ))) / (1 - δ))
        (𝓝[>] (0 : ℝ)) (𝓝 n)) := by sorry

end Supplement

end SparseHistComm
