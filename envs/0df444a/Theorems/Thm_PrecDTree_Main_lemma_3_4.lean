-- Prove2me | Theorems.Thm_PrecDTree_Main_lemma_3_4
-- name    : PrecDTree.Main.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:52:41.842129+00:00
-- url     : https://prove2.me/theorems/e8c62e89-f212-45c2-9768-84d822db51a0
-- title:
--   Lemma 3.4 — the covering universe U_ξ misses at most one hypothesis and has at least 4/5 · |H| elements
-- statement:
--   Let $H$ be a finite set of hypotheses with $|H|\ge2$ and $T$ a family of tests separating every two distinct hypotheses of $H$. With $\xi(t)=\{h\in H\mid h\in X$ for some reply $X$ of $t$ with $|X|\le\frac34|H|\}$ and $U_\xi=\bigcup_t\xi(t)$,
--   $$|U_\xi|\ \ge\ |H|-1\qquad\text{and}\qquad |U_\xi|\ \ge\ \tfrac45\,|H| .$$
--   The lemma guarantees that a cover of a quarter of $U_\xi$ covers at least $|H|/5$ hypotheses, which is what makes each call of Algorithm 1 shrink the hypothesis set by a constant factor.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: a set of hypotheses H and tests T (§3, p. 6) → hypothesis Identifiable T Hs (every two distinct hypotheses separated by some test); reason: the domain of the decision-tree problem; the proof uses it ('By definition we know that there exists a test which distinguishes h1 and h2')
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 6, Lemma 3.4

import Mathlib
import Definitions.Def_PrecDTree_Main_Xi

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Lemma 3.4** (p. 6). If `|H| ≥ 2`, then `|U_ξ| ≥ |H| − 1` and `|U_ξ| ≥ 4/5 · |H|`. -/
theorem lemma_3_4 {m : ℕ} {H : Type} [DecidableEq H] (T : Fin m → H → ℕ) (Hs : Finset H)
    (hid : Identifiable T Hs) (hn : 2 ≤ Hs.card) :
    (Hs.card : ℝ) - 1 ≤ ((Uxi T Hs).card : ℝ) ∧
      (4 : ℝ) / 5 * (Hs.card : ℝ) ≤ ((Uxi T Hs).card : ℝ) := by sorry

end PrecDTree.Main
