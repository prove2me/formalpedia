-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_2_basic_solution
-- name    : PairwiseRealize.sec_A_2_basic_solution
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:36.097255+00:00
-- url     : https://prove2.me/theorems/9ff29e7b-c8cc-42cd-8e22-5c7ffa82af4c
-- title:
--   §A.2, p.12 — a rational basic solution at a node, with at most $d$ fractional entries
-- statement:
--   Let $g_1,\dots,g_k\in\mathbb Z^d$, $q^0\in\{0,1\}^k$, and $T\ge0$ with $T\sqrt d\le k/32768$. Suppose the event of Lemma A.1 holds: the closed Euclidean ball of radius $k/32768$ lies in $\{\sum_a(p_a-q^0_a)g_a:p\in[0,1]^k\}$. Then every $e\in\mathbb Z^d$ with $|e_i|\le T$ for all $i$ can be written $\sum_a(p_a-q^0_a)g_a=e$ with a rational $p\in[0,1]^k$ that has at most $d$ entries outside $\{0,1\}$.
--
--   This is the local linear system solved at each node of the repair hierarchy.
--
--   Differences from the source:
--   - generalization: G_R with entries in {−1, 0, 1}; k_R and T_R of a node with C₀ ≥ 32768 → any integer columns; any k and real T ≥ 0 with T√d ≤ k/32768; reason: the page derives T_R√d_R ≤ k_R/32768 from k_R and C₀, and its columns are integer
--   - encoding: a "rational basic solution" → its stated consequences: rational, at most d fractional entries; reason: the page uses basicness only through them
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, p.12 (PDF p.13); §3.2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PairwiseRealize_Bundles

namespace PairwiseRealize

/-- **A rational basic solution at a node, §A.2 p.12 (PDF p.13); §3.2 p.7 (PDF p.8).** K. Shi,
H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript
sha256 62090516…): "For a node R, let G_R ∈ {−1, 0, 1}^{d_R×k_R} be the matrix whose columns are the
pair-count changes of its reserved rectangle switches. Let q⁰ ∈ {0, 1}^{k_R} be the baseline
orientation vector. On the event in Lemma A.1, any incoming e ∈ [−T_R, T_R]^{d_R} ∩ ℤ^{d_R} has a
rational basic solution p ∈ [0, 1]^{k_R} to G_R(p − q⁰) = e, with at most d_R fractional entries:
‖e‖₂ ≤ T_R√d_R ≤ k_R/32768, since C0 ≥ 32768."

Let `g₁, …, g_k ∈ ℤ^d` (coordinates indexed by a finite set `ι` of size `d`), `q⁰ ∈ {0,1}^k`, and
`T ≥ 0` with `T√d ≤ k/32768`. If the event of Lemma A.1 holds, i.e. the closed Euclidean ball of
radius `k/32768` lies in `{Σₐ (pₐ − q⁰ₐ) gₐ : p ∈ [0, 1]^k}`, then every `e ∈ ℤ^d` with
`|e_i| ≤ T` for all `i` is `Σₐ (pₐ − q⁰ₐ) gₐ` for a rational `p ∈ [0, 1]^k` with at most `d`
entries outside `{0, 1}`.

**Formalization Note** "Basic" is used on the page only through its consequences (rational, at most
`d_R` fractional entries), which are stated. The columns may be any integer vectors (the page's are
in `{−1, 0, 1}`), and the size condition is `T√d ≤ k/32768`, which the page derives from
`k_R ≥ C0(T_R⌈√d_R⌉ + …)` and `C0 ≥ 32768`. -/
theorem sec_A_2_basic_solution {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : Fin k → ι → ℤ)
    (q0 : Fin k → Bool) (T : ℝ) (hT : 0 ≤ T)
    (hTk : T * Real.sqrt (Fintype.card ι) ≤ (k : ℝ) / 32768)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ ι) ((k : ℝ) / 32768) ⊆
      {y | ∃ p : Fin k → ℝ, (∀ a, p a ∈ Set.Icc (0 : ℝ) 1) ∧
        y = ∑ a, (p a - bitR (q0 a)) • WithLp.toLp 2 (fun i => (g a i : ℝ))})
    (e : ι → ℤ) (he : ∀ i, |(e i : ℝ)| ≤ T) :
    ∃ p : Fin k → ℚ, (∀ a, 0 ≤ p a ∧ p a ≤ 1) ∧
      (∀ i, ∑ a, (p a - (bv (q0 a) : ℚ)) * (g a i : ℚ) = (e i : ℚ)) ∧
      (Finset.univ.filter fun a => p a ≠ 0 ∧ p a ≠ 1).card ≤ Fintype.card ι := by sorry

end PairwiseRealize
