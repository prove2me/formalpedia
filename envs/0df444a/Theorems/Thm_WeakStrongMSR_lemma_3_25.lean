-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_25
-- name    : WeakStrongMSR.lemma_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:37.244461+00:00
-- url     : https://prove2.me/theorems/a1ba3be7-b74b-4ddf-80ba-2408e790cadb
-- title:
--   Lemma 3.25 (general $\delta$) — whp, from any $x$ at most $(\tfrac12-\tfrac34\gamma)|A|$ edges into a union $A$ of $\le j$ true balls with $|A|\ge cjh$ are corrupted
-- statement:
--   Let $\gamma=\tfrac12-\delta$ and let $h$ be the witness count of Eq. (20).
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there is $n_0$ with the following property, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$ and metric $d$. With probability at least $1-2/n$ over the corruption set, the following holds simultaneously for every $1\le j\le ck$, every point $x$ and every union $A$ of at most $j$ true metric balls with $|A|\ge cjh$:
--   $$\#\{v\in A\setminus\{x\}:\{x,v\}\text{ corrupted}\}\le\Big(\tfrac12-\tfrac34\gamma\Big)|A|.$$
--
--   At $\delta=1/3$ the factor is the main text's $3/8$. The bound is uniform over all unions of balls, so it applies to sets chosen using weak distances.
--
--   Differences from the source:
--   - generalization: main text: δ = 1/3, factor 3/8, h = 32⌈c log n/32⌉ → every δ ∈ (0, 1/2), factor a = 1/2 − 3γ/4, h per Eq. (20); reason: App. A, p.35 states this form; at δ = 1/3, a = 3/8
--   - reading: "with high probability"; "c sufficiently large" → probability ≥ 1 − 2/n for n ≥ n₀, ∃ c₀ ∀ c ≥ c₀, c₀ and n₀ independent of δ; reason: the main-text proof gives "at most 2/n" (p.23); App. A applies the same union bound
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.25, p.23 (PDF 24); App. A, p.35 (PDF 36), "Repair"

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.25** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.23, PDF p.24; general-δ form, App. A, p.35, PDF p.36).
"With high probability, simultaneously for every 1 ≤ j ≤ ck, point x ∈ X, and set A ⊆ X expressible as
a union of at most j true metric balls with |A| ≥ cjh, at most 3|A|/8 edges from x to A \ {x} are
corrupted." (p.35: "Let a := 1/2 − 3γ/4. For a point x and a union A of at most j true balls with
|A| ≥ cjh, … Pr[more than a|A| edges from x to A \ {x} are corrupted] ≤ e^{−γ²|A|/8}".)

There is an absolute `c₀` such that for every `c ≥ c₀` there is `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1` and metric `d`, with probability at least `1 − 2/n` over the
corruption set, for every `1 ≤ j ≤ ck`, every point `x` and every union `A` of at most `j` balls
`B(c_i, r_i)` with `|A| ≥ cjh`, at most `(1/2 − 3γ/4)|A|` of the pairs `{x, v}`, `v ∈ A ∖ {x}`,
are corrupted, where `γ = 1/2 − δ` and `h = hParam c δ n`.

**Formalization Note.** At `δ = 1/3` the factor `1/2 − 3γ/4` is the main text's `3/8`. The bound
`2/n` is the main text's (p.23); the general-δ proof gives the same union bound. Balls are pairs
(centre, radius); a ball of negative radius is empty and changes no union. -/
theorem lemma_3_25 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d →
      1 - 2 / (n : ℝ) ≤ corrProb δ (fun C : Finset (Sym2 (Fin n)) =>
        ∀ j : ℕ, 1 ≤ j → j ≤ c * k → ∀ x : Fin n, ∀ B : List (MinSumRadiiPTAS.Main.Ball n),
          B.length ≤ j →
          ((c * j * hParam c δ n : ℕ) : ℝ) ≤
            ((B.toFinset.biUnion (fun b => b.pts d)).card : ℝ) →
          ((((B.toFinset.biUnion (fun b => b.pts d)).erase x).filter
              (fun v => s(x, v) ∈ C)).card : ℝ) ≤
            (1 / 2 - 3 * (1 / 2 - δ) / 4) *
              ((B.toFinset.biUnion (fun b => b.pts d)).card : ℝ)) := by sorry

end WeakStrongMSR
