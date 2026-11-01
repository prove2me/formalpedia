-- Prove2me | Theorems.Thm_SubmodOrder_single_threshold
-- name    : SubmodOrder.single_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:07.498452+00:00
-- url     : https://prove2.me/theorems/fb476d67-5028-4a64-9cbd-f4d55840c0db
-- title:
--   Proof of Theorem 2, p.21 — a threshold in $[(1-\varepsilon)\mathrm{OPT}/(2k),\,\mathrm{OPT}/(2k)]$ gives $f(S)\ge(1-\varepsilon)\tfrac12\mathrm{OPT}$
-- statement:
--   Let $f$ be monotone with $f(\emptyset)=0$ and weak submodular order $\pi$, let $k\ge1$ and $\varepsilon\in(0,1)$, and let $\mathrm{OPT}=\max\{f(T):|T|\le k\}$. If the threshold $\tau$ satisfies
--
--   $$
--   \frac{(1-\varepsilon)\,\mathrm{OPT}}{2k}\ \le\ \tau\ \le\ \frac{\mathrm{OPT}}{2k},
--   $$
--
--   then the output $S$ of Threshold Add$(k,\tau)$ satisfies
--
--   $$
--   f(S)\ \ge\ (1-\varepsilon)\cdot\tfrac12\cdot\mathrm{OPT}.
--   $$
--
--   This is the core of the proof of Theorem 2: Algorithm 1 tries a geometric grid of thresholds, one of which lies in this window.
--
--   Differences from the source:
--   - generalization: f monotone and subadditive, τ = τ_i a grid threshold of Algorithm 1 → f monotone, no subadditivity, every real τ in the window; reason: the argument uses neither subadditivity nor the grid, only the window; it specializes to the paper's f
--   - encoding: OPT, the optimal value of max f(S) over |S| ≤ k → StreamSubmod.optVal f k (published definition, reused), a finite maximum over the subsets of the Fintype α with at most k elements; reason: same value; ∅ is feasible, so the family is nonempty
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21, "We show that f(Si) ≥ (1 − ε)0.5OPT."

import Mathlib
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd

namespace SubmodOrder

/-- One good threshold suffices (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21: "there
exists an i such that (1 − ε)OPT/(2k) ≤ τi ≤ OPT/(2k). We show that f(Si) ≥ (1 − ε)0.5OPT.").

Let `f` be monotone with `f(∅) = 0` and weak submodular order `π`, let `k ≥ 1` and `ε ∈ (0,1)`.
For every threshold `τ` with `(1 − ε) OPT/(2k) ≤ τ ≤ OPT/(2k)`, the output `S` of
Threshold Add(k, τ) satisfies `f(S) ≥ (1 − ε) · ½ · OPT`, where
`OPT = max {f(T) : |T| ≤ k}`.

**Formalization Note.** `(1−ε)0.5` is the product `(1 − ε) · (1/2)`. -/
theorem single_threshold {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (π : α ≃ Fin n)
    (f : Finset α → ℝ) (hmono : Monotone f) (hf0 : f ∅ = 0) (hπ : IsWeakSubmodularOrder f π)
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (τ : ℝ)
    (hτl : (1 - ε) * StreamSubmod.optVal f k / (2 * k) ≤ τ)
    (hτu : τ ≤ StreamSubmod.optVal f k / (2 * k)) :
    (1 - ε) * (1 / 2) * StreamSubmod.optVal f k ≤ f (OracleProg.run f (thresholdAdd π k τ)).1 := by sorry

end SubmodOrder
