-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_sample_path_bound
-- name    : StaticQuote.Clairvoyant.sample_path_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:10.065983+00:00
-- url     : https://prove2.me/theorems/342958f4-95ac-4b20-b2bf-96bc1ac15f97
-- title:
--   p. 18, proof of Theorem 4 — γ_{1:M}(ω)/M ≤ Σ_{n=1}^M g(D_n − d_n)/M on every sample path
-- statement:
--   Let $y$ be an FCFS-feasible schedule: on every sample path, $y_n \ge t_n$ and $y_{n+1}\ge y_n+x_n$ for all $n\ge1$, with departure times $D_n = y_n + x_n$. Let $\gamma_{1:M}(\omega)$ be the perfectly-clairvoyant cost (12) of the first $M$ customers. Then for every sample path $\omega$ and every $M$,
--   $$\frac{\gamma_{1:M}(\omega)}{M} \le \frac{\sum_{n=1}^M g(D_n - d_n)}{M}.$$
--
--   The clairvoyant program relaxes every information constraint, so the first $M$ start times of any feasible schedule are feasible for it. This is the pathwise first step of the proof of Theorem 4.
--
--   **Formalization Note.** No probabilistic assumption is used. The page's "$\forall M\in\mathbb N$" starts at $M=1$; at $M=0$ both sides are $0$ in $[0,\infty]$, so the statement is given for every $M$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, proof of Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, proof of Theorem 4 (sample-path bound): for every FCFS-feasible schedule `y`, every
sample path `ω` and every `M`, `γ_{1:M}(ω)/M ≤ Σ_{n=1}^M g(D_n − d_n)/M` with `D_n = y_n + x_n`.

**Formalization Note.** Pathwise; no probabilistic hypothesis is needed because both sides are in
`ℝ≥0∞` with summands `ENNReal.ofReal (g …)`. The page's "∀M ∈ ℕ" starts at 1; at `M = 0` both
sides are `0`, so the statement is given for every `M`. The schedule class `IsFCFSSchedule`
contains every policy of the paper's class Π. -/
theorem sample_path_bound {Ω : Type*} [MeasurableSpace Ω] (Q : Model Ω)
    (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) (ω : Ω) (M : ℕ) :
    Q.gamma 1 M ω / (M : ℝ≥0∞) ≤
      (∑ n ∈ Finset.Icc 1 M, ENNReal.ofReal (g Q.ce Q.cd (y n ω + Q.x n ω - Q.due n ω))) /
        (M : ℝ≥0∞) := by sorry

end StaticQuote.Clairvoyant
