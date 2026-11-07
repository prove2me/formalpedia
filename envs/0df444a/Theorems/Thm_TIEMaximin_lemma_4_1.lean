-- Prove2me | Theorems.Thm_TIEMaximin_lemma_4_1
-- name    : TIEMaximin.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:45:52.472197+00:00
-- url     : https://prove2.me/theorems/c6b10520-15ce-425a-8c91-8602126442b9
-- title:
--   Lemma 4.1 — the reservation lottery
-- statement:
--   Let $m\ge n\ge2$, $\alpha\in(0,1)$, $v$ a nonnegative profile, and $D$ ordered by decreasing $1/k_i$. There is a finite lottery over 0–1 points of (12) whose mean is exactly $(h,p)$. In every outcome, with $R$ the set of reserved goods,
--
--   $$|R\setminus P_t|\le\lceil\rho(P_t)\rceil\qquad(0\le t\le m)$$
--
--   and
--
--   $$\sum_{i\text{ a dummy agent}}\frac1{k_i}\le\max_{i\in D}\frac1{k_i}+\sum_{i\in D}\frac{p_i}{k_i}\le1,$$
--
--   where an empty maximum is zero.
--
--   This is the first step of the mechanism. The first bound caps the goods reserved outside every comparison set, and the second makes the compensation feasible.
--
--   Differences from the source:
--   - generalization: in every outcome of the lottery → for every 0–1 point of (12); reason: every outcome is such a point, so this specializes to the source; the page's proof shows exactly this ("Every vertex satisfies (C)", "(D) is exactly its prefix hypothesis")
--   - reading: Order D by decreasing 1/k_i (ties unspecified) → every order `ord` with `IsDOrder`; reason: the page does not break ties
--   - encoding: finite lottery → `PMF` on a finite type, expectations as finite sums; reason: a distribution on a finite type is finite; same instances
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 4.1, eqs. (13), (14), p.20

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Reservation

namespace TIEMaximin

open Finset

/-- **Lemma 4.1** (p.20). There is a finite lottery over 0–1 points of (12) whose mean is exactly `(h,
p)`. In every outcome, with `R` the set of reserved goods, `|R ∖ P_t| ≤ ⌈ρ(P_t)⌉` for `0 ≤ t ≤ m`
(13), and `Σ_{i a dummy agent} 1/k_i ≤ max_{i∈D} 1/k_i + Σ_{i∈D} p_i/k_i ≤ 1` (14), an empty
maximum being zero.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 4.1, eqs. (13), (14), p.20.

**Formalization Note.** Stated for every `α ∈ (0,1)` (p.10) and every order of `D` by decreasing
`1/k_i` (`ord`). (13) and (14) are stated for every 0–1 point of (12), which covers every outcome
of every such lottery; the page's proof shows exactly this ("Every vertex satisfies (C)"; "(D) is
exactly its prefix hypothesis"). -/
theorem lemma_4_1 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (v : Fin n → Fin m → ℝ) (hv : Nonneg v) (ord : List (Fin n)) (hord : IsDOrder α v ord) :
    (∃ μ₁ : PMF (ResPt n m),
      (∀ pt ∈ μ₁.support, IsResPoint α v ord pt) ∧
      (∀ i g, expect μ₁ (fun pt => if pt.1 i g = true then 1 else 0) = hRet α v i g) ∧
      (∀ i, expect μ₁ (fun pt => if pt.2 i = true then 1 else 0) = pDef α v i)) ∧
    ∀ pt : ResPt n m, IsResPoint α v ord pt →
      (∀ t, t ≤ m → ((#(reserved pt \ prefixP v t) : ℕ) : ℤ) ≤ ⌈rho α v (prefixP v t)⌉) ∧
      (∑ i with pt.2 i = true, 1 / (kDef α v i : ℝ) ≤
        (if h : (defSet α v).Nonempty then (defSet α v).sup' h (fun i => 1 / (kDef α v i : ℝ)) else 0) +
          ∑ i ∈ defSet α v, pDef α v i / (kDef α v i : ℝ)) ∧
      ((if h : (defSet α v).Nonempty then (defSet α v).sup' h (fun i => 1 / (kDef α v i : ℝ)) else 0) +
          ∑ i ∈ defSet α v, pDef α v i / (kDef α v i : ℝ) ≤ 1) := by sorry

end TIEMaximin
