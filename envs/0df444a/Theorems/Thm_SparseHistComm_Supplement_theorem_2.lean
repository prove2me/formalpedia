-- Prove2me | Theorems.Thm_SparseHistComm_Supplement_theorem_2
-- name    : SparseHistComm.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:43:29.187283+00:00
-- url     : https://prove2.me/theorems/ee7010a0-09ef-4a31-b313-6b3f5041ac17
-- title:
--   Theorem 2 — heterogeneous communication characterization
-- statement:
--   Fix $n\ge1$, $k\ge1$, $0\le D<k$, and $0\le\delta<1$. There are constants $C>0$ and $d_0$ (depending on these fixed parameters but not on $d$) such that for every $d\ge d_0$,
--
--   $$
--   \left|C_{\mathrm{het}}(D,\delta)
--     -(1-\delta)(nk-\lfloor nD\rfloor)\log_2 d\right|
--     \le C\log_2\log_2 d.
--   $$
--
--   In addition, for every $d\ge\max\{2,nk\}$,
--
--   $$
--   C_{\mathrm{het}}(D,\delta)\ge
--   (1-\delta)(nk-\lfloor nD\rfloor)\log_2d-nk\log_2(2nk)-1
--   -n\log_2\!\bigl(e(k\lceil\log_2d\rceil+1)\bigr).
--   $$
--
--   Thus heterogeneous encoders have the exact first-order coefficient furnished by the optimal total covering level, together with the paper's finite-dimensional lower bound.
--
--   Differences from the source:
--   - encoding: $O(\log\log d)$ for fixed $n,k,D,\delta$ → positive $C$ and threshold $d_0$ with an absolute-error bound for every $d\ge d_0$; reason: this is the standard literal quantifier form of the printed big-O equality
--   - encoding: real-valued $C_{\mathrm{het}}$ → an $\mathbb R_{\ge0}\cup\{\infty\}$ infimum, with eventual finiteness stated before conversion to $\mathbb R$; reason: nonintegrable or unbounded protocols cannot acquire Lean's junk value zero
--   - encoding: $\lceil\log_2 d\rceil$ → `Nat.clog 2 d`; reason: this is the exact natural ceiling of the base-two logarithm for $d\ge2$
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 2, p.9, (19)–(20); proof pp.16–18

import Mathlib
import Definitions.Def_SparseHistComm_threshold
import Definitions.Def_SparseHistComm_Supplement_Chet

open Filter Topology
open scoped ENNReal

namespace SparseHistComm

namespace Supplement

/-- **Theorem 2 (Heterogeneous communication characterization)** (Ye–Fan, *Optimal Communication
for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256
29df82a4…f27c6f), p.9, (19)–(20)). This includes both the fixed-parameter
`O(log log d)` characterization and the explicit lower bound for every `d ≥ max{2,nk}`.

**Formalization Note** The `O(log log d)` constant may depend on the fixed `n,k,D,δ`, but not on
`d`; it is represented by `C` and `d₀`. Eventual finiteness is stated before `ENNReal.toReal` is
used. All unmarked logarithms are base two, and `Nat.clog 2 d` is `⌈log₂ d⌉`. -/
theorem theorem_2 (n k : ℕ) (D δ : ℝ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hD0 : 0 ≤ D) (hDk : D < k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Supplement.Chet n k d D δ ≠ ⊤ ∧
      |(Supplement.Chet n k d D δ).toReal -
          (1 - δ) * (threshold n k D : ℝ) * Real.logb 2 d| ≤
        C * Real.logb 2 (Real.logb 2 d)) ∧
    ∀ d : ℕ, max 2 (n * k) ≤ d →
      ENNReal.ofReal ((1 - δ) * (threshold n k D : ℝ) * Real.logb 2 d -
        n * k * Real.logb 2 (2 * n * k) - 1 -
        n * Real.logb 2 (Real.exp 1 * (k * Nat.clog 2 d + 1))) ≤
        Supplement.Chet n k d D δ := by sorry

end Supplement

end SparseHistComm
