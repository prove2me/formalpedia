-- Prove2me | Theorems.Thm_TIESharp_lemma_4_5
-- name    : TIESharp.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:19.1936+00:00
-- url     : https://prove2.me/theorems/a1fd191c-c327-4d00-ab74-d202b9cf452b
-- title:
--   Lemma 4.5 — bounded consistent kernels imply locality
-- statement:
--   Let $n\ge2$. Suppose bounded measurable kernels $h_{i,k}:((0,\infty)^n)^{k+1}\to\mathbb R$, $0\le k\le n-2$, symmetric in their last $k$ arguments almost everywhere, give the expansion (4.14) for every job count $m\ge1$:
--   $$q^{m,*}_{i1}(t)=\sum_{k=0}^{\min(n-2,\,m-1)}\ \sum_{J\subseteq\{2,\dots,m\},\ |J|=k}h_{i,k}(t_{\cdot1};t_J).$$
--   If the resulting $q^{m,*}_{i1}$ lie in $[0,1]$ almost everywhere on $(0,\infty)^{n\times m}$ for every $m$, then $h_{i,k}=0$ almost everywhere for every $1\le k\le n-2$.
--
--   Adding many independent jobs from a box would make a nonzero correction kernel grow like a polynomial in their number, which a probability cannot do.
--
--   Differences from the source:
--   - reading: the resulting q^{m,*}_ij lie in [0, 1] almost everywhere → the expansion (4.14) of the distinguished job lies in [0, 1] a.e. for every m and i; reason: (4.14) defines only the distinguished job's probability; the others are its job permutations
--   - encoding: kernels h_{i,k} : ((0,∞)^n)^{k+1} → R, bounded measurable → h i k : (Fin n → ℝ) → (Fin k → Fin n → ℝ) → ℝ, measurable and bounded by a constant for k ≤ n − 2; jobs Fin (m+1) with distinguished job 0; reason: same kernels; only orders k ≤ n − 2 enter (4.14)
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.5, p.21, with (4.14), p.21

import Mathlib
import Definitions.Def_TIESharp_kernelExpansion

set_option autoImplicit false

open MeasureTheory

namespace TIESharp

/-- **Lemma 4.5 (Bounded consistent kernels imply locality)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 4.5, p.21). Let `n ≥ 2`. Suppose
bounded measurable kernels `h_{i,k} : ((0, ∞)^n)^{k+1} → ℝ`, `0 ≤ k ≤ n − 2`, symmetric in their
last `k` arguments almost everywhere, give the expansion (4.14) for every job count `m ≥ 1`:
`q^{m,*}_{i1}(t) = Σ_{k=0}^{min(n−2, m−1)} Σ_{J ⊆ {2,…,m}, |J| = k} h_{i,k}(t_{·1}; t_J)`. If the
resulting `q^{m,*}_{i1}` lie in `[0, 1]` almost everywhere on `(0, ∞)^{n×m}` for every `m`, then
`h_{i,k} = 0` almost everywhere for every `1 ≤ k ≤ n − 2`.

**Formalization Note.** A kernel of order `k` is `h i k x u` with `x` the distinguished column and
`u : Fin k → Fin n → ℝ` the other `k` columns; "almost everywhere" is Lebesgue measure on
`(Fin n → ℝ) × (Fin k → Fin n → ℝ)` restricted to the positive orthant. Jobs are `Fin (m + 1)`
with distinguished job `0` (`kernelExpansion`). The probabilities `q^{m,*}_{ij}` of the other jobs
are not defined by (4.14), so the `[0, 1]` hypothesis is on the expansion of the distinguished
job. Kernels of order `k > n − 2` do not enter (4.14) and carry no hypothesis. -/
theorem lemma_4_5 (n : ℕ) (hn : 2 ≤ n)
    (h : Fin n → (k : ℕ) → (Fin n → ℝ) → (Fin k → Fin n → ℝ) → ℝ)
    (hmeas : ∀ i k, k ≤ n - 2 → Measurable (Function.uncurry (h i k)))
    (hbdd : ∀ i k, k ≤ n - 2 → ∃ B : ℝ, ∀ x u, |h i k x u| ≤ B)
    (hsymm : ∀ i k, k ≤ n - 2 → ∀ σ : Equiv.Perm (Fin k),
      ∀ᵐ p ∂(volume.restrict
          {p : (Fin n → ℝ) × (Fin k → Fin n → ℝ) | (∀ a, 0 < p.1 a) ∧ ∀ l a, 0 < p.2 l a}),
        h i k p.1 (fun l => p.2 (σ l)) = h i k p.1 p.2)
    (hq : ∀ (m : ℕ) (i : Fin n),
      ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin (m + 1) → ℝ | ∀ a j, 0 < t a j}),
        0 ≤ kernelExpansion h m i t ∧ kernelExpansion h m i t ≤ 1) :
    ∀ (i : Fin n) (k : ℕ), 1 ≤ k → k ≤ n - 2 →
      (fun p : (Fin n → ℝ) × (Fin k → Fin n → ℝ) => h i k p.1 p.2)
        =ᵐ[volume.restrict
          {p : (Fin n → ℝ) × (Fin k → Fin n → ℝ) | (∀ a, 0 < p.1 a) ∧ ∀ l a, 0 < p.2 l a}] 0 := by sorry

end TIESharp
