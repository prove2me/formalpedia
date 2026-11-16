-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_1_9
-- name    : SetDefinedGraphs.Supplement.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:45:46.090227+00:00
-- url     : https://prove2.me/theorems/ce6870d0-6d44-4dd5-9f13-bf21018d5872
-- title:
--   Theorem 1.9 — $J(d,A)$ is $\chi$-unbounded iff some $a\le b<c$ satisfy (i)–(iv); then $S_3\subseteq J(d,A)$, and $S_2\subseteq J(d,A)$ when $a=b$ works
-- statement:
--   Let $d\in\mathbb N$ and $A\subseteq[0,d-1]$, and let $J(d,A)$ be the class of $(d,A)$-generalized Johnson graphs (vertices carry distinct $d$-sets $S_v$; distinct $u,v$ are adjacent iff $|S_u\cap S_v|\in A$). The class $J(d,A)$ is $\chi$-unbounded if and only if there exist $a,b,c\in[0,d]$ such that
--
--   1. $a\le b<c$,
--   2. $a,b,c\notin A$,
--   3. $a+1\in A$, and
--   4. $c-b\in\bigl[1,\lfloor\tfrac{d-b}{2}\rfloor\bigr]$.
--
--   Moreover, if $J(d,A)$ is $\chi$-unbounded, then $S_3\subseteq J(d,A)$. If the conditions above can be satisfied with $a=b$, then $S_2\subseteq J(d,A)$.
--
--   This gives a complete arithmetic characterisation of $\chi$-boundedness for generalized Johnson graphs, including Kneser and Johnson graphs, with shift graphs as the witnesses of unboundedness.
--
--   **Formalization Note** $[0,d]=\{0,\dots,d\}$; $c-b$ and $\lfloor (d-b)/2\rfloor$ are computed in $\mathbb N$, exactly since $b<c\le d$.
--
--   Differences from the source:
--
--   - encoding: J(d, A): graphs with an assignment of distinct d-sets S_v → finite graphs G : SimpleGraph W ([Finite W]) with an injective S : W → Finset ℕ, |S v| = d; reason: the paper's graphs are finite; a finite graph needs finitely many ground elements, so ℕ as ground set loses nothing
--   - encoding: S_D ⊆ J(d, A) → every graph isomorphic to the underlying graph of an induced subdigraph of S⃗(n, D) is in J(d, A); reason: S_D is the class of induced subgraphs of S(n, D), the underlying graph of S⃗(n, D) (p.2, p.15); J(d, A) is isomorphism-closed
--   - encoding: a, b, c ∈ [0, d]; c − b ∈ [1, ⌊(d−b)/2⌋] → naturals a, b, c ≤ d; 1 ≤ c − b ∧ c − b ≤ (d − b) / 2 in ℕ; reason: b < c ≤ d, so the subtractions are exact and ℕ division is the floor
--   - encoding: χ(G), ω(G) of a graph → Mathlib chromaticNumber (in ℕ∞) and cliqueNum; reason: the graphs are finite, so these are the paper's parameters
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.9, p.5 (PDF p.7); restated p.76 (PDF p.78); J(d, A) defined p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Supplement_Johnson

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 1.9** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.5, PDF p.7; restated p.76, PDF p.78): let `d ∈ ℕ` and `A ⊆ [0, d − 1]`. The class
`J(d, A)` is χ-unbounded if and only if there exist `a, b, c ∈ [0, d]` such that
(i) `a ≤ b < c`, (ii) `a, b, c ∉ A`, (iii) `a + 1 ∈ A`, and (iv) `c − b ∈ [1, ⌊(d − b)/2⌋]`.
Moreover, if `J(d, A)` is χ-unbounded, then `S_3 ⊆ J(d, A)`. If the conditions above can be satisfied with `a = b`,
then `S_2 ⊆ J(d, A)`.

**Formalization Note** `[0, d]` is `{0, …, d}` (naturals); `c − b` is natural subtraction, exact since `b < c`, and
`⌊(d − b)/2⌋` is natural division, with `b < c ≤ d`. -/
theorem theorem_1_9 (d : ℕ) (A : Set ℕ) (hA : ∀ x ∈ A, x < d) :
    (¬ IsChiBoundedGraphClass (InJohnson d A) ↔
      ∃ a b c : ℕ, a ≤ d ∧ b ≤ d ∧ c ≤ d ∧ a ≤ b ∧ b < c ∧ a ∉ A ∧ b ∉ A ∧ c ∉ A ∧ a + 1 ∈ A ∧
        1 ≤ c - b ∧ c - b ≤ (d - b) / 2) ∧
    (¬ IsChiBoundedGraphClass (InJohnson d A) → ContainsShiftGraphs 3 (InJohnson d A)) ∧
    ((∃ a c : ℕ, a ≤ d ∧ c ≤ d ∧ a < c ∧ a ∉ A ∧ c ∉ A ∧ a + 1 ∈ A ∧
        1 ≤ c - a ∧ c - a ≤ (d - a) / 2) → ContainsShiftGraphs 2 (InJohnson d A)) := by sorry

end SetDefinedGraphs.Supplement
