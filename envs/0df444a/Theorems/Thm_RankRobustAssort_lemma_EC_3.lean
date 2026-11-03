-- Prove2me | Theorems.Thm_RankRobustAssort_lemma_EC_3
-- name    : RankRobustAssort.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:39.505206+00:00
-- url     : https://prove2.me/theorems/7366184a-1e74-4413-a1dd-cf7568e338ea
-- title:
--   Lemma EC.3 (corrected: $i\ne j$) — a consistent ranking can prefer $i$ to $j$ iff $j\not\prec i$
-- statement:
--   Let $(i_1,\dots,i_M)\in\mathcal L$ and let $i,j\in\mathcal N_0$ be **distinct**. Then there exists a ranking $\sigma\in\bigcap_{m\in\mathcal M}\mathcal D_{i_m}(S_m)$ with $\sigma(i)<\sigma(j)$ if and only if
--
--   $$
--   j\not\prec_{i_1\cdots i_M} i.
--   $$
--
--   Reachability in $\mathcal G_{i_1\cdots i_M}$ thus encodes exactly the pairwise preferences forced by the tuple: if $i$ has a path to $j$, every ranking corresponding to the tuple prefers $j$ to $i$, and otherwise some such ranking prefers $i$ to $j$.
--
--   Differences from the source:
--   - correction: $i,j\in\mathcal N_0$ → $i,j\in\mathcal N_0$ with $i\ne j$; reason: false as printed for $i=j$: with $n=1$, $M=1$, $S_1=\{0,1\}$, $v_1=(1/2,1/2)$, $\eta=0$ and the tuple $(0)\in\mathcal L$, the left side asks for $\sigma(0)<\sigma(0)$ while $0\not\prec 0$ holds; the proof of Lemma EC.4 uses the lemma only for $i\ne j$
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.3, p.ec15

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Reach

namespace RankRobustAssort

/-- **Lemma EC.3** (corrected: `i ≠ j`). Let `(i₁,…,i_M) ∈ ℒ` and `i, j ∈ 𝒩₀` with `i ≠ j`. Then
there exists a ranking `σ ∈ ⋂_{m∈ℳ} 𝒟_{i_m}(S_m)` that satisfies `σ(i) < σ(j)` if and only if
`j ⊀_{i₁⋯i_M} i`.

Sturt, arXiv:2112.05010v4, Lemma EC.3, p.ec15.

Formalization Note: the printed lemma has no `i ≠ j`, and is false for `i = j`: the left side
`σ(i) < σ(i)` is false while `i ⊀ i` holds for every tuple in `ℒ` (the graph is acyclic). Example:
`n = 1`, `M = 1`, `S₁ = {0,1}`, `v₁ = (½,½)`, `η = 0`, tuple `(0)`, `i = j = 0`. The hypothesis
`i ≠ j` is the minimal correction; Lemma EC.4's proof uses the lemma only with `i ≠ j`.
`σ ∈ ⋂_m 𝒟_{i_m}(S_m)` is `∀ m, IsTop σ (S m) (t m)`. -/
theorem lemma_EC_3 {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (ht : InL P t)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    (∃ σ : Equiv.Perm (Fin (n + 1)), (∀ m, IsTop σ (P.S m) (t m)) ∧ σ i < σ j) ↔
      ¬ Reach P t j i := by sorry

end RankRobustAssort
