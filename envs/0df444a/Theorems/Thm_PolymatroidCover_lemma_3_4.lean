-- Prove2me | Theorems.Thm_PolymatroidCover_lemma_3_4
-- name    : PolymatroidCover.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:40.376722+00:00
-- url     : https://prove2.me/theorems/173b1c29-b569-48e0-9da8-4716dc229b96
-- title:
--   Lemma 3.4 — an adding pair always exists when $k = (2d-1)\chi^\circ(f) - (2d-2)$
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a $d$-polymatroid with no self-loops ($f(e) > 0$ for every $e$, the standing assumption of §2), let
--
--   $$
--   k = (2d - 1)\cdot\chi^\circ(f) - (2d - 2),
--   $$
--
--   let $S_1 \sqcup \dots \sqcup S_k$ be a valid $k$-coloring of $S \subseteq E$ and $h \in E \setminus S$.
--
--   **Lemma 3.4.** Suppose $T = (T^1, \dots, T^{i-1})$ is a valid search sequence with respect to the current coloring and the algorithm is attempting to build the $i$-th layer. Then there is an adding pair $(a, j)$ satisfying the condition of Step 5:
--
--   $$
--   a \in B(T) \cup \{h\}, \qquad f(a \mid A_j \cup B_j) = f(a).
--   $$
--
--   This is the step where the number of colors $k$ enters: it guarantees that the search can always be extended.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: $k := (2d-1)\cdot\chi^\circ(f) - (2d-2)$ → a natural number `k` with `(k : ℤ) = (2d − 1)·χ°(f) − (2d − 2)`; reason: under the hypotheses ($h$ exists and has $f(h) > 0$) the right side is at least 1, so this is the same $k$
--   - encoding: $\chi^\circ(f)$, the maximum in (1) → `chiCirc f`, a `Finset.sup` of natural ceilings `⌈·⌉₊` over the $T$ with $f(T) > 0$; reason: for a polymatroid every ratio in (1) is nonnegative and here the index set is nonempty ($f(E) \ge f(h) > 0$), so the sup is the max
--   - encoding: colorings $S_1 \sqcup \dots \sqcup S_k$ and search sequences $(T^1, T^2, \dots)$ with 1-based colors and layers → `col : Fin k → Finset (Fin n)` and `List (Layer n k)`, 0-based ($T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)`, $T^{\le i}$ is `T.take i`); reason: the same objects, reindexed
--   - encoding: the (inclusion-wise) minimal minimizer of (8) → any `R` with `IsMinimalMinimizer` (minimizer over the stated domain, no proper subset a minimizer); reason: for a submodular objective it is unique (Lemma 2.3), so the instances are the same
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Lemma 3.4, p.15 (PDF p.17); proof p.16

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_chiCirc
import Definitions.Def_PolymatroidCover_IsValidColoring
import Definitions.Def_PolymatroidCover_IsValidSeq

namespace PolymatroidCover

/-- Lemma 3.4 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.2, printed p.15 = PDF p.17; proof printed p.16): suppose
`T = (T^1, …, T^{i−1})` is a valid sequence with respect to the current coloring
`S_1 ⊔ ⋯ ⊔ S_k`, and is attempting to build the `i`-th layer. Then there exists an adding
pair `(a, j)` satisfying the conditions of Step 5.

**Formalization Note** The §3 setting is in the binders: `f` is a `d`-polymatroid without
self-loops (standing assumption, printed p.9), `k = (2d − 1)·χ°(f) − (2d − 2)` (printed p.11,
as an equation in `ℤ`), `col` is a valid `k`-coloring of `S` and `h ∉ S`. The adding pair is
for all layers of `T` (the paper's `A_j = A_j^{<i}`, `B_j = B_j^{<i}`). -/
theorem lemma_3_4 {n : ℕ} (d k : ℕ) (f : Finset (Fin n) → ℕ) (hf : IsDPolymatroid d f)
    (hloop : ∀ e : Fin n, 0 < f {e})
    (hk : (k : ℤ) = (2 * (d : ℤ) - 1) * (chiCirc f : ℤ) - (2 * (d : ℤ) - 2))
    (S : Finset (Fin n)) (col : Fin k → Finset (Fin n)) (hcol : IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S) (T : List (Layer n k)) (hT : IsValidSeq f h col T) :
    ∃ (a : Fin n) (j : Fin k), IsAddingPair f h T a j := by sorry

end PolymatroidCover
