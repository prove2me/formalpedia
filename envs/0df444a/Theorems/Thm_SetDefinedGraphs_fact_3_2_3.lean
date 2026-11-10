-- Prove2me | Theorems.Thm_SetDefinedGraphs_fact_3_2_3
-- name    : SetDefinedGraphs.fact_3_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:54.440956+00:00
-- url     : https://prove2.me/theorems/7ed481d1-97c0-449b-bed4-1c75a2373d06
-- title:
--   Fact 3.2(3) — $\vec{\mathcal S}_d\supsetneq\vec{\mathcal S}_{d+1}$
-- statement:
--   For each $d\ge2$, let $\vec{\mathcal S}_d$ be the class of $d$-dimensional shift digraphs (induced subdigraphs of $\vec S(n,d)$, $n\ge1$, up to isomorphism). Then
--   $$\vec{\mathcal S}_d\supsetneq\vec{\mathcal S}_{d+1}:$$
--   1. every $(d+1)$-dimensional shift digraph is a $d$-dimensional shift digraph, and
--   2. some $d$-dimensional shift digraph is not a $(d+1)$-dimensional shift digraph.
--
--   In particular every higher-dimensional shift digraph is a shift digraph, which justifies calling $\vec{\mathcal S}_2$ the class of shift digraphs.
--
--   Differences from the source:
--
--   - reading: "For each d" → for each d ≥ 2; reason: S⃗_d is defined only for d ≥ 2 (p.2: "For integers n, d ∈ ℕ with d ≥ 2")
--   - encoding: [n] = {1, …, n} → Fin n = {0, …, n−1}; reason: order isomorphism; same digraphs
--   - encoding: induced subdigraphs of S⃗(n, d) for n ≥ 1, as a class up to isomorphism → ∃ n : ℕ (n = 0 allowed) and a subset S, G isomorphic to the induced subdigraph on S; reason: S⃗(0, d) is empty, an induced subdigraph of S⃗(1, d); same class
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Fact 3.2(3), p.15 (PDF p.17); proof pp.15–16

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Fact 3.2(3)** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §3.2, p.15, PDF p.17): for each `d`, `S⃗_d ⊋ S⃗_{d+1}`. Here `S⃗_d` is the class of
`d`-dimensional shift digraphs (induced subdigraphs of `S⃗(n, d)`, `n ≥ 1`, up to isomorphism), defined for `d ≥ 2`.

**Formalization Note** Both halves are stated: every `(d+1)`-dimensional shift digraph is a `d`-dimensional one, and
some `d`-dimensional shift digraph is not `(d+1)`-dimensional. -/
theorem fact_3_2_3 (d : ℕ) (hd : 2 ≤ d) :
    (∀ {W : Type} (G : Digraph W), IsShiftDigraphDim (d + 1) G → IsShiftDigraphDim d G) ∧
      ∃ (W : Type) (G : Digraph W), IsShiftDigraphDim d G ∧ ¬ IsShiftDigraphDim (d + 1) G := by sorry

end SetDefinedGraphs
