-- Prove2me | Theorems.Thm_PolymatroidCover_lemma_3_13
-- name    : PolymatroidCover.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:56.008429+00:00
-- url     : https://prove2.me/theorems/3b40afb0-a283-416a-9d06-97e25b177c39
-- title:
--   Lemma 3.13 — Algorithm 1 terminates within $2^{|E|}$ iterations
-- statement:
--   Throughout, $f : 2^E \to \mathbb Z_{\ge 0}$ is a polymatroid with no self-loops ($f(e) > 0$ for every $e$, the standing assumption of §2), $S_1 \sqcup \dots \sqcup S_k$ is a valid $k$-coloring of a set $S \subseteq E$, and $h \in E \setminus S$ is the element being inserted (the input of Algorithm 1). For a search sequence $T = (T^1, \dots, T^{i-1})$, $A_j$ and $B_j$ denote the adding elements and the union of the blocking sets of the layers with proposed color $j$, $B(T)$ the union of all blocking sets, and $\tilde f(X \mid Y) = \tilde f(X \cup Y) - \tilde f(Y)$ the conditional deficiency.
--
--   **Lemma 3.13.** Algorithm 1 terminates in $2^{|E|}$ iterations of the while-loop.
--
--   Precisely: let $(C_0, T_0), \dots, (C_m, T_m)$ be the states at the head of the while-loop along any run, with $C_0$ the input coloring and $T_0$ the empty sequence, each obtained from the previous one by an iteration that does not return (an iteration runs from Step 5 to the next build, every collapse and re-entry of Step 6 included, and the adding pair of Step 5 is chosen arbitrarily). Then
--
--   $$
--   m < 2^{|E|},
--   $$
--
--   so every run makes at most $2^{|E|}$ iterations in total, the last one being the returning one.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: colorings $S_1 \sqcup \dots \sqcup S_k$ and search sequences $(T^1, T^2, \dots)$ with 1-based colors and layers → `col : Fin k → Finset (Fin n)` and `List (Layer n k)`, 0-based ($T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)`, $T^{\le i}$ is `T.take i`); reason: the same objects, reindexed
--   - encoding: the (inclusion-wise) minimal minimizer of (8) → any `R` with `IsMinimalMinimizer` (minimizer over the stated domain, no proper subset a minimizer); reason: for a submodular objective it is unique (Lemma 2.3), so the instances are the same
--   - reading: "the algorithm" (Algorithm 1; Step 5 fixes no choice rule, line 23 re-enters Step 6) → every run of the iteration relation `Iter`: header states from $(S_1 \sqcup \dots \sqcup S_k, \emptyset)$, each iteration from Step 5 to the next build or return with every collapse inside it, any Step 5 choice; reason: Step 5 leaves $(a, j)$ open, so a claim about the algorithm must hold for every choice; line 23 jumps to Step 6, not to line 4
--   - encoding: "terminates in $2^{|E|}$ iterations" → every run has $m < 2^n$ iterations that do not return; reason: an iteration either ends with a build or returns, and the returning one is the last, so this is at most $2^{|E|}$ iterations in total
--   - generalization: $f$ a $d$-polymatroid and $k = (2d-1)\chi^\circ(f) - (2d-2)$ (the setting of §3) → any polymatroid $f$ and any number of colors $k$; reason: neither the statement nor its proof uses $d$ or the value of $k$; with $k$ set to the §3 value the Lean statement is the paper's
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Lemma 3.13, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PolymatroidCover_IsPolymatroid
import Definitions.Def_PolymatroidCover_IsValidColoring
import Definitions.Def_PolymatroidCover_Iter

namespace PolymatroidCover

/-- Lemma 3.13 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.4, printed p.20 = PDF p.22): the algorithm terminates in `2^{|E|}`
iterations of the while-loop.

**Formalization Note** The standing hypotheses of §3 are binders: `f` is a polymatroid with no self-loops
(`∀ e, 0 < f {e}`, the standing assumption of §2, printed p.9), `col` is a valid coloring of
`S` (`col j` is `S_{j+1}`) and `h ∉ S` (the input of Algorithm 1, printed pp.11, 14).
The number of colors `k` is arbitrary: the argument never uses the value of `k`. A run is a sequence of header states `(cols i, Ts i)`,
`i = 0, …, m`, from the input coloring and the empty search sequence, each reached from the
previous one by a while-loop iteration (`Iter`, with any choice in Step 5) that does not return;
a collapse and the re-entry of Step 6 (line 23) belong to the same iteration. The conclusion
`m < 2^n` says that every run makes fewer than `2^{|E|}` non-returning iterations, hence at most
`2^{|E|}` iterations in total, the last one being the returning one. -/
theorem lemma_3_13 {n k : ℕ} (f : Finset (Fin n) → ℕ) (hf : IsPolymatroid f) (hloop : ∀ e : Fin n, 0 < f {e})
    (S : Finset (Fin n)) (col : Fin k → Finset (Fin n)) (hcol : IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S)
    (m : ℕ) (cols : ℕ → Fin k → Finset (Fin n)) (Ts : ℕ → List (Layer n k))
    (h0 : cols 0 = col ∧ Ts 0 = [])
    (hrun : ∀ i < m, Iter f h (cols i) (Ts i) (.next (cols (i + 1)) (Ts (i + 1)))) :
    m < 2 ^ n := by sorry

end PolymatroidCover
