-- Prove2me | Theorems.Thm_SetMultCost_lemma_4_4
-- name    : SetMultCost.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:04.280541+00:00
-- url     : https://prove2.me/theorems/ad1accec-21f9-4159-ac5f-0e81e57350d9
-- title:
--   Lemma 4.4 (corrected: $a_j,b_j\in\mathbb N$ in $m$-good) — an $m$-good $\alpha$ gives lower bounds
-- statement:
--   Let $d\ge2$, let $\tau=(\tau_0,\dots,\tau_\ell)$ be non-decreasing with $\tau_\ell<d$ and $\tau_0=1$, let $S\subseteq[\ell]$ and $m\ge0$, and let $\alpha\in(0,1]$ with $n^\alpha\ge d$ be $m$-good for $(\tau,S)$. Then for every partition $\pi$ of $[d]$ and any set-multilinear $(\tau,S)$-product $G_1\cdots G_r$,
--
--   $$\mathrm{relrk}_{n,\alpha,\pi}(G_1\cdots G_r)\le2\,n^{-m/2},$$
--
--   and if a polynomial is a sum of $s$ such products, its relative rank is at most $2s\,n^{-m/2}$.
--
--   This reduces lower bounds to the arithmetic question of finding good pairs $\alpha,\tau$.
--
--   Differences from the source:
--   - correction: m-good with positive integers a_j, b_j → m-good with a_j, b_j ∈ ℕ; reason: with positive integers the lemma is false: τ = (1,1), S = {1}, d = 2, G₁G₂ = x·y, P = {1}, N = {2}, α = 1 has relrk = 1/n while every α is vacuously m-good for every m
--   - reading: n^{−Ω(m)} and s·n^{−Ω(m)} → 2·n^{−m/2} and 2s·n^{−m/2}; reason: the proof gives this form; it implies the constant 1/4 for m ≥ 1, n ≥ 16, while a uniform n^{−Ω(m)} without the 2 fails as m → 0
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 4.4, p.15; Definition 4.3, pp.14–15

import Mathlib
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_relrk
import Definitions.Def_SetMultCost_IsTauSProduct
import Definitions.Def_SetMultCost_IsMGood

namespace SetMultCost

/-- **Lemma 4.4.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.15: "Let d ≥ 2. Suppose τ = (τ0, . . . , τℓ) ∈ N^{ℓ+1}_{≥0} be a
non-decreasing sequence with τℓ < d and τ0 = 1. Let S ⊆ [ℓ], m ≥ 0 and α ∈ (0, 1] be a real number
such that n^α ≥ d and α is m-good for (τ,S). Then, for every partition π = P ⊔ N of [d] and for any
set-multilinear (τ,S)-product G1 · · · Gr, we have relrkn,α,π(G1 · · · Gr) ≤ n^{−Ω(m)}. Consequently,
if a set-multilinear polynomial Φ has a (τ,S)-product-decomposition of size s, then relrkn,α,π(Φ) ≤
s · n^{−Ω(m)}."

**Formalization Note.** `n^{−Ω(m)}` is the proof's explicit form `2 · n^{−m/2}` (p.15), and the
second bound is `2s · n^{−m/2}`. A uniform `n^{−Ω(m)}` with no factor `2` fails as `m → 0`; for
`m ≥ 1`, `n ≥ 16` this implies constant `1/4`. `m`-good is the corrected `IsMGood`. -/
theorem lemma_4_4 (F : Type*) [Field F] {d n : ℕ} (hd : 2 ≤ d) (ℓ : ℕ) (τ : ℕ → ℕ)
    (hτ : MonotoneOn τ (Set.Iic ℓ)) (hτd : τ ℓ < d) (hτ0 : τ 0 = 1) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 ℓ) (m : ℝ) (hm : 0 ≤ m) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hn : (d : ℝ) ≤ (n : ℝ) ^ α) (hgood : IsMGood α m τ S) (P : Finset (Fin d)) :
    (∀ G : List (MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F),
      IsSetMultilinearProduct Sigma.fst Finset.univ G → IsTauSProduct τ S G →
      relrk n α P Finset.univ G.prod ≤ 2 * (n : ℝ) ^ (-(m / 2))) ∧
    (∀ (s : ℕ) (Gs : Fin s → List (MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F)),
      (∀ i, IsSetMultilinearProduct Sigma.fst Finset.univ (Gs i)) →
      (∀ i, IsTauSProduct τ S (Gs i)) →
      relrk n α P Finset.univ (∑ i, (Gs i).prod) ≤ 2 * (s : ℝ) * (n : ℝ) ^ (-(m / 2))) := by sorry

end SetMultCost
