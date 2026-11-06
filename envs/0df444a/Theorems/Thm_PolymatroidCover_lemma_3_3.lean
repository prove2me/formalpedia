-- Prove2me | Theorems.Thm_PolymatroidCover_lemma_3_3
-- name    : PolymatroidCover.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:02.432206+00:00
-- url     : https://prove2.me/theorems/e8fa391c-5ce7-4126-97f5-cba8ec136f77
-- title:
--   Lemma 3.3 — $f(A_j^{<i} \cup B_j^{<i}) \le \sum_{e} f(e) - |A_j^{<i}|$
-- statement:
--   Throughout, $f : 2^E \to \mathbb Z_{\ge 0}$ is a polymatroid with no self-loops ($f(e) > 0$ for every $e$, the standing assumption of §2), $S_1 \sqcup \dots \sqcup S_k$ is a valid $k$-coloring of a set $S \subseteq E$, and $h \in E \setminus S$ is the element being inserted (the input of Algorithm 1). For a search sequence $T = (T^1, \dots, T^{i-1})$, $A_j$ and $B_j$ denote the adding elements and the union of the blocking sets of the layers with proposed color $j$, $B(T)$ the union of all blocking sets, and $\tilde f(X \mid Y) = \tilde f(X \cup Y) - \tilde f(Y)$ the conditional deficiency.
--
--   **Lemma 3.3.** Let $T = (T^1, \dots, T^{i-1})$ be a valid search sequence with respect to the current coloring $S_1 \sqcup \dots \sqcup S_k$. Then for every color $j$,
--
--   $$
--   f\big(A_j^{<i} \cup B_j^{<i}\big) \le \sum_{e \in A_j^{<i} \cup B_j^{<i}} f(e) - \big|A_j^{<i}\big|.
--   $$
--
--   Each layer of color $j$ has a nonempty blocking set, which costs at least one unit of rank; this bound feeds the counting argument of Lemma 3.4.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: colorings $S_1 \sqcup \dots \sqcup S_k$ and search sequences $(T^1, T^2, \dots)$ with 1-based colors and layers → `col : Fin k → Finset (Fin n)` and `List (Layer n k)`, 0-based ($T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)`, $T^{\le i}$ is `T.take i`); reason: the same objects, reindexed
--   - encoding: the (inclusion-wise) minimal minimizer of (8) → any `R` with `IsMinimalMinimizer` (minimizer over the stated domain, no proper subset a minimizer); reason: for a submodular objective it is unique (Lemma 2.3), so the instances are the same
--   - generalization: $f$ a $d$-polymatroid and $k = (2d-1)\chi^\circ(f) - (2d-2)$ (the setting of §3) → any polymatroid $f$ and any number of colors $k$; reason: neither the statement nor its proof uses $d$ or the value of $k$; with $k$ set to the §3 value the Lean statement is the paper's
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Lemma 3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PolymatroidCover_IsPolymatroid
import Definitions.Def_PolymatroidCover_IsValidColoring
import Definitions.Def_PolymatroidCover_IsValidSeq

namespace PolymatroidCover

/-- Lemma 3.3 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.2, printed p.15 = PDF p.17): if `T = (T^1, …, T^{i−1})` is a valid
sequence with respect to the current coloring `S_1 ⊔ ⋯ ⊔ S_k`, then for each color `j`
```
f(A_j^{<i} ∪ B_j^{<i}) ≤ ∑_{e ∈ A_j^{<i} ∪ B_j^{<i}} f(e) − |A_j^{<i}|.
```

**Formalization Note** The standing hypotheses of §3 are binders: `f` is a polymatroid with no self-loops
(`∀ e, 0 < f {e}`, the standing assumption of §2, printed p.9), `col` is a valid coloring of
`S` (`col j` is `S_{j+1}`) and `h ∉ S` (the input of Algorithm 1, printed pp.11, 14).
The number of colors `k` is arbitrary: the argument never uses the value of `k`. The inequality is in `ℤ`; `A_j^{<i}`, `B_j^{<i}` are `addSet T j`,
`blockSet T j` (all layers of `T`). -/
theorem lemma_3_3 {n k : ℕ} (f : Finset (Fin n) → ℕ) (hf : IsPolymatroid f) (hloop : ∀ e : Fin n, 0 < f {e})
    (S : Finset (Fin n)) (col : Fin k → Finset (Fin n)) (hcol : IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S)
    (T : List (Layer n k)) (hT : IsValidSeq f h col T) (j : Fin k) :
    (f (addSet T j ∪ blockSet T j) : ℤ) ≤
      (∑ e ∈ addSet T j ∪ blockSet T j, (f {e} : ℤ)) - ((addSet T j).card : ℤ) := by sorry

end PolymatroidCover
