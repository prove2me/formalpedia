-- Prove2me | Theorems.Thm_QAlgorithms_Childs_adversary_compose_le
-- name    : QAlgorithms.Childs.adversary_compose_le
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:33:16.537466+00:00
-- url     : https://prove2.me/theorems/036e84ed-01b5-4c62-898a-ed381d3d6cf2
-- title:
--   Adversary bound of a composed function is at most the product
-- statement:
--   Let $f : \{0,1\}^n \to \{0,1\}$ and $g : \{0,1\}^m \to \{0,1\}$ be total Boolean functions, and let $f \circ g : \{0,1\}^{nm} \to \{0,1\}$ be the block composition
--
--   $$(f\circ g)(y) = f\big(g(y^1), \dots, g(y^n)\big),$$
--
--   where $y = (y^1, \dots, y^n)$ with each block $y^i \in \{0,1\}^m$. With $\mathrm{Adv}^{\pm}$ the general adversary bound (24.1), taken over the full domains,
--
--   $$\mathrm{Adv}^{\pm}(f \circ g) \le \mathrm{Adv}^{\pm}(f)\,\mathrm{Adv}^{\pm}(g).$$
--
--   This composition upper bound, combined with the dual solutions for OR and AND, gives $\mathrm{Adv}^{\pm} \le \sqrt n$ for balanced binary AND-OR trees.
--
--   **Formalization Note** Input positions of $f \circ g$ are indexed by pairs $(i,j)$ (bit $j$ of block $i$) over arbitrary finite index types; this is the source's consecutive-block layout up to the relabelling $(i,j) \mapsto (i-1)m + j$, under which $\mathrm{Adv}^{\pm}$ is invariant. $\mathrm{Adv}^{\pm}$ is valued in $[0,\infty]$ and is $0$ for constant functions.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 126, Theorem 24.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.Childs

open scoped NNReal ENNReal


/-- Childs, Theorem 24.2 (PDF p. 126): for total `f : {0,1}^n → {0,1}` and
`g : {0,1}^m → {0,1}`, `Adv±(f ∘ g) ≤ Adv±(f) Adv±(g)`, where
`(f ∘ g)(y) = f(g(y¹), …, g(yⁿ))` with `yⁱ ∈ {0,1}^m` the `i`-th block of `y`. The composed input
is indexed by `ι × κ`, `y (i, j)` being bit `j` of block `i`. -/
theorem adversary_compose_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool) :
    advPm (blockCompose f g) Finset.univ ≤ advPm f Finset.univ * advPm g Finset.univ := by
  sorry


end QAlgorithms.Childs
