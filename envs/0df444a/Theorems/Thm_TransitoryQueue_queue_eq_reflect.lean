-- Prove2me | Theorems.Thm_TransitoryQueue_queue_eq_reflect
-- name    : TransitoryQueue.queue_eq_reflect
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:32.179635+00:00
-- url     : https://prove2.me/theorems/1b67d6e0-6eb9-4e47-96cc-38d2f853618f
-- title:
--   (117)–(118) (corrected: up to runs of zero services) — the queue length is the reflection of $Y_n$
-- statement:
--   Fix a sample of size $n\ge1$ with epochs $T_i>0$, indicators $\zeta_i\in\{0,1\}$, service requirements $V_i\ge0$, an efficiency $c>0$, a constant $\mu>0$ and any function $\hat H$. Let
--
--   $$Y_n(t)=\Bigl(\frac{A_n(t)}{\sqrt n}-\hat H(t)\Bigr)+\frac{c}{\sqrt n}\Bigl(\frac{D_n(t)}{\mu}-\frac{M_n(D_n(t))}{c}\Bigr)+\Bigl(\hat H(t)-\frac{c}{\sqrt n}\frac t\mu\Bigr)\qquad(116)$$
--
--   and let $R$ be the longest run of zeros among $V_1,\dots,V_n$. Then for every $t\ge0$, with $I_n(t)=t-D_n(t)$,
--
--   $$\Bigl|\frac{c}{\sqrt n\,\mu}I_n(t)+\inf_{0\le s\le t}Y_n(s)\Bigr|\le\frac R{\sqrt n},\qquad\Bigl|\frac{Q_n(t)}{\sqrt n}-\phi(Y_n)(t)\Bigr|\le\frac R{\sqrt n}.$$
--
--   When no service requirement is zero ($R=0$) these are the equalities (117) and (118).
--
--   Differences from the source:
--   - correction: (117) (c_n/(√nµ)) I_n(t) = −inf_{s≤t} Y_n(s) and (118) Q_n(t)/√n = φ(Y_n)(t) → both hold up to R/√n, R the longest run of zero service requirements; reason: with zero services (allowed: Assumption 2.7's V_i are non-negative) they fail: n = 2, p = 1, c_n = 1, V_1 = 1, V_2 = 0, T_2 > T_1 + 1; on [T_1 + 1, T_2), A_n = 1, D_n = 1, M_n(1) = 2, so Q_n = −1 by (6) while φ(Y_n) ≥ 0
--   - encoding: the random processes of §7 → a fixed sample path: T_i > 0, ζ_i ∈ {0, 1}, V_i ≥ 0, any μ > 0 and any Ĥ; reason: the identities are deterministic; T_i > 0 holds almost surely by Remark 2.6, and Ĥ cancels in (116)
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eqs. (116)–(118), p.38

import Mathlib
import Definitions.Def_TransitoryQueue_arrivals
import Definitions.Def_TransitoryQueue_completed
import Definitions.Def_TransitoryQueue_busy
import Definitions.Def_TransitoryQueue_queue
import Definitions.Def_TransitoryQueue_reflect
import Definitions.Def_TransitoryQueue_zeroRun

namespace TransitoryQueue

/-- **(117)–(118), corrected (the queue length is the reflection of `Y_n`, up to zero services).**
Fix a sample `T_i > 0`, `ζ_i ∈ {0, 1}`, `V_i ≥ 0` of size `n ≥ 1`, an efficiency `c > 0`, a mean
`μ > 0` and any function `Ĥ`. Let
`Y_n(t) = (A_n(t)/√n - Ĥ(t)) + (c/√n)(D_n(t)/μ - M_n(D_n(t))/c) + (Ĥ(t) - (c/√n)(t/μ))` (116)
and let `R` be the longest run of zeros in `V_1, …, V_n`. Then for all `t ≥ 0`, with
`I_n(t) = t - D_n(t)`:
`|(c/(√n μ)) I_n(t) + inf_{s≤t} Y_n(s)| ≤ R/√n` and `|Q_n(t)/√n - φ(Y_n)(t)| ≤ R/√n`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eqs. (116)–(118), p.38, corrected.

**Formalization Note** The page asserts the equalities (117) and (118). They hold when no `V_i`
is `0` (`R = 0`) but fail otherwise: with `n = 2`, `c = 1`, `V_1 = 1`, `V_2 = 0`, `T_2 > T_1 + 1`,
on `[T_1 + 1, T_2)` (6) gives `Q_n = -1 < 0 ≤ φ(Y_n)`. Assumption 2.7 allows `V_i = 0`
("non-negative"). `Ĥ` cancels in (116); it is kept to match the page. -/
theorem queue_eq_reflect (n : ℕ) (hn : 1 ≤ n) (T : Fin n → ℝ) (ζ : Fin n → ℕ) (V : Fin n → ℝ)
    (c μ : ℝ) (Hh : ℝ → ℝ) (hT : ∀ i, 0 < T i) (hζ : ∀ i, ζ i ≤ 1) (hV : ∀ i, 0 ≤ V i)
    (hc : 0 < c) (hμ : 0 < μ) (t : ℝ) (ht : 0 ≤ t) :
    let Y : ℝ → ℝ := fun s =>
      ((arrivals T ζ s : ℝ) / Real.sqrt n - Hh s)
        + c / Real.sqrt n * (busy c T ζ V s / μ - (completed c V (busy c T ζ V s) : ℝ) / c)
        + (Hh s - c / Real.sqrt n * (s / μ))
    |c / (Real.sqrt n * μ) * (t - busy c T ζ V t) + ⨅ s : Set.Icc (0 : ℝ) t, Y s|
        ≤ (zeroRun V : ℝ) / Real.sqrt n ∧
      |queue c T ζ V t / Real.sqrt n - reflect Y t| ≤ (zeroRun V : ℝ) / Real.sqrt n := by sorry

end TransitoryQueue
