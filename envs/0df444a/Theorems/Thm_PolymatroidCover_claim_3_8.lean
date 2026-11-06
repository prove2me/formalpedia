-- Prove2me | Theorems.Thm_PolymatroidCover_claim_3_8
-- name    : PolymatroidCover.claim_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:43.101923+00:00
-- url     : https://prove2.me/theorems/40065719-a54c-4a16-89e8-95d4ab7b6571
-- title:
--   Claim 3.8 — layers of color $j'$ keep their blocking sets after the recoloring
-- statement:
--   Throughout, $f : 2^E \to \mathbb Z_{\ge 0}$ is a polymatroid with no self-loops ($f(e) > 0$ for every $e$, the standing assumption of §2), $S_1 \sqcup \dots \sqcup S_k$ is a valid $k$-coloring of a set $S \subseteq E$, and $h \in E \setminus S$ is the element being inserted (the input of Algorithm 1). For a search sequence $T = (T^1, \dots, T^{i-1})$, $A_j$ and $B_j$ denote the adding elements and the union of the blocking sets of the layers with proposed color $j$, $B(T)$ the union of all blocking sets, and $\tilde f(X \mid Y) = \tilde f(X \cup Y) - \tilde f(Y)$ the conditional deficiency.
--
--   **The collapse step.** Suppose $T = (T^1, \dots, T^{i-1})$ is valid for the current coloring, $(a, j)$ is the adding pair chosen in Step 5, and the blocking set $R$ computed in Step 6 is empty. If $a \ne h$, let $i'$ be the layer with $a \in B(T^{i'})$, $j' = c(T^{i'})$ and $a' = A(T^{i'})$; the algorithm recolors $a$ from $j'$ to $j$, giving $S'_j = S_j \cup \{a\}$, $S'_{j'} = S_{j'} \setminus \{a\}$, and cuts the sequence to $(T^1, \dots, T^{i'-1})$.
--
--   **Claim 3.8.** Assume $a \ne h$. For every layer $t < i'$ with color $c(T^t) = j'$, its blocking set $B^t_{j'}$ is the minimal minimizer of
--
--   $$
--   \min_{X \subseteq S'_{j'} \setminus B^{<t}_{j'}} \tilde f\big(X \mid A^{\le t}_{j'} \cup B^{<t}_{j'}\big), \qquad S'_{j'} = S_{j'} \setminus \{a\}.
--   $$
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: colorings $S_1 \sqcup \dots \sqcup S_k$ and search sequences $(T^1, T^2, \dots)$ with 1-based colors and layers → `col : Fin k → Finset (Fin n)` and `List (Layer n k)`, 0-based ($T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)`, $T^{\le i}$ is `T.take i`); reason: the same objects, reindexed
--   - encoding: the (inclusion-wise) minimal minimizer of (8) → any `R` with `IsMinimalMinimizer` (minimizer over the stated domain, no proper subset a minimizer); reason: for a submodular objective it is unique (Lemma 2.3), so the instances are the same
--   - encoding: the collapse index $i'$, $j' = c(T^{i'})$, $a' = A(T^{i'})$ → any 0-based `i' < T.length` with `a ∈ (T[i']).block`; $j'$, $a'$ read off `T[i']`; reason: $i'$ is unique by Fact 2, so the instances are the same
--   - generalization: $f$ a $d$-polymatroid and $k = (2d-1)\chi^\circ(f) - (2d-2)$ (the setting of §3) → any polymatroid $f$ and any number of colors $k$; reason: neither the statement nor its proof uses $d$ or the value of $k$; with $k$ set to the §3 value the Lean statement is the paper's
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Claim 3.8, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PolymatroidCover_IsPolymatroid
import Definitions.Def_PolymatroidCover_IsValidColoring
import Definitions.Def_PolymatroidCover_IsValidSeq

namespace PolymatroidCover

/-- Claim 3.8 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.3, printed p.18 = PDF p.20): for every layer `t < i'` with color
`c(T^t) = j'`, its blocking set `B_{j'}^t` is the minimal minimizer of
```
min_{X ⊆ S'_{j'} \ B_{j'}^{<t}} f̃(X | A_{j'}^{≤t} ∪ B_{j'}^{<t}),
```
where `S'_{j'} = S_{j'} \ {a}`.

**Formalization Note** The standing hypotheses of §3 are binders: `f` is a polymatroid with no self-loops
(`∀ e, 0 < f {e}`, the standing assumption of §2, printed p.9), `col` is a valid coloring of
`S` (`col j` is `S_{j+1}`) and `h ∉ S` (the input of Algorithm 1, printed pp.11, 14).
The number of colors `k` is arbitrary: the argument never uses the value of `k`. The collapse context of printed p.17 (PDF p.19) is spelled out: `T` (the paper's
`(T^1, …, T^{i−1})`) is valid for the current coloring, `(a, j)` is the adding pair of Step 5,
and the blocking set `R` of Step 6 is empty (`IsBlockingSet f col T a j ∅`). For `a ≠ h`,
`i'` is any 0-based layer index with `a ∈ B(T^{i'})` (unique by Fact 2), `j' = c(T^{i'})` and
`a' = A(T^{i'})`. The claim is stated under `a ≠ h` ("We assume below that
`a ≠ h`", printed p.18). Layers are 0-based: `T[t]` is the paper's `T^{t+1}`, so
`A_{j'}^{≤t}` is `addSet (T.take (t+1)) j'` and `B_{j'}^{<t}` is `blockSet (T.take t) j'`. -/
theorem claim_3_8 {n k : ℕ} (f : Finset (Fin n) → ℕ) (hf : IsPolymatroid f) (hloop : ∀ e : Fin n, 0 < f {e})
    (S : Finset (Fin n)) (col : Fin k → Finset (Fin n)) (hcol : IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S)
    (T : List (Layer n k)) (hT : IsValidSeq f h col T)
    (a : Fin n) (j : Fin k) (hpair : IsAddingPair f h T a j) (hR : IsBlockingSet f col T a j ∅)
    (hah : a ≠ h) (i' : ℕ) (hi' : i' < T.length) (ha : a ∈ (T[i']'hi').block) :
    ∀ (t : ℕ) (ht : t < i'), (T[t]'(ht.trans hi')).color = (T[i']'hi').color →
      IsMinimalMinimizer
        (fun X => deficCond f X
          (addSet (T.take (t + 1)) (T[i']'hi').color ∪ blockSet (T.take t) (T[i']'hi').color))
        ((col (T[i']'hi').color).erase a \ blockSet (T.take t) (T[i']'hi').color)
        (T[t]'(ht.trans hi')).block := by sorry

end PolymatroidCover
