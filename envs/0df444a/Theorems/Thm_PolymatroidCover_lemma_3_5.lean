-- Prove2me | Theorems.Thm_PolymatroidCover_lemma_3_5
-- name    : PolymatroidCover.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:40.907315+00:00
-- url     : https://prove2.me/theorems/c98e64a7-8e30-4c33-892b-fc1fcd7498f1
-- title:
--   Lemma 3.5 — an empty blocking set gives $f(a) = f(a \mid A_j^{<i} \cup S_j)$
-- statement:
--   Throughout, $f : 2^E \to \mathbb Z_{\ge 0}$ is a polymatroid with no self-loops ($f(e) > 0$ for every $e$, the standing assumption of §2), $S_1 \sqcup \dots \sqcup S_k$ is a valid $k$-coloring of a set $S \subseteq E$, and $h \in E \setminus S$ is the element being inserted (the input of Algorithm 1). For a search sequence $T = (T^1, \dots, T^{i-1})$, $A_j$ and $B_j$ denote the adding elements and the union of the blocking sets of the layers with proposed color $j$, $B(T)$ the union of all blocking sets, and $\tilde f(X \mid Y) = \tilde f(X \cup Y) - \tilde f(Y)$ the conditional deficiency.
--
--   **Lemma 3.5.** Suppose $T = (T^1, \dots, T^{i-1})$ is a valid search sequence with respect to the current coloring and the algorithm is attempting to build the $i$-th layer. Let $(a, j)$ be the adding pair chosen in Step 5. If the blocking set $R$ computed in Step 6 is empty, then
--
--   $$
--   f(a) = f\big(a \mid A_j^{<i} \cup S_j\big).
--   $$
--
--   In particular $S_j \cup \{a\}$ is independent, which is what makes the recoloring of a collapse step valid.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: colorings $S_1 \sqcup \dots \sqcup S_k$ and search sequences $(T^1, T^2, \dots)$ with 1-based colors and layers → `col : Fin k → Finset (Fin n)` and `List (Layer n k)`, 0-based ($T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)`, $T^{\le i}$ is `T.take i`); reason: the same objects, reindexed
--   - encoding: the (inclusion-wise) minimal minimizer of (8) → any `R` with `IsMinimalMinimizer` (minimizer over the stated domain, no proper subset a minimizer); reason: for a submodular objective it is unique (Lemma 2.3), so the instances are the same
--   - generalization: $f$ a $d$-polymatroid and $k = (2d-1)\chi^\circ(f) - (2d-2)$ (the setting of §3) → any polymatroid $f$ and any number of colors $k$; reason: neither the statement nor its proof uses $d$ or the value of $k$; with $k$ set to the §3 value the Lean statement is the paper's
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Lemma 3.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_PolymatroidCover_IsPolymatroid
import Definitions.Def_PolymatroidCover_IsValidColoring
import Definitions.Def_PolymatroidCover_IsValidSeq

namespace PolymatroidCover

/-- Lemma 3.5 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.3, printed p.17 = PDF p.19): suppose `T = (T^1, …, T^{i−1})` is a
valid sequence with respect to the current coloring `S_1 ⊔ ⋯ ⊔ S_k`, and is attempting to build
the `i`-th layer. Let `(a, j)` be the adding pair chosen in Step 5. If the set `R` defined on
Step 6 is empty, then `f(a) = f(a | A_j^{<i} ∪ S_j)`.

**Formalization Note** The standing hypotheses of §3 are binders: `f` is a polymatroid with no self-loops
(`∀ e, 0 < f {e}`, the standing assumption of §2, printed p.9), `col` is a valid coloring of
`S` (`col j` is `S_{j+1}`) and `h ∉ S` (the input of Algorithm 1, printed pp.11, 14).
The number of colors `k` is arbitrary: the argument never uses the value of `k`. "`R` is empty" is `IsBlockingSet f col T a j ∅` (`∅` is the
minimal minimizer of Step 6). `f(a | ·)` is `marg f {a} ·` in `ℤ`. -/
theorem lemma_3_5 {n k : ℕ} (f : Finset (Fin n) → ℕ) (hf : IsPolymatroid f) (hloop : ∀ e : Fin n, 0 < f {e})
    (S : Finset (Fin n)) (col : Fin k → Finset (Fin n)) (hcol : IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S)
    (T : List (Layer n k)) (hT : IsValidSeq f h col T)
    (a : Fin n) (j : Fin k) (hpair : IsAddingPair f h T a j) (hR : IsBlockingSet f col T a j ∅) :
    marg f {a} (addSet T j ∪ col j) = (f {a} : ℤ) := by sorry

end PolymatroidCover
