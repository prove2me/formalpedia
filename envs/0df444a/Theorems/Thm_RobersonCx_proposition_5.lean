-- Prove2me | Theorems.Thm_RobersonCx_proposition_5
-- name    : RobersonCx.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:24.667017+00:00
-- url     : https://prove2.me/theorems/6497f3c2-c0f9-41a5-a563-26364b1ea4b0
-- title:
--   Proposition 5 — congruences modulo infinitely many integers give $H\in\mathrm{Cl}(\mathcal F)$
-- statement:
--   Let $H$ be a graph, $S$ an infinite set of positive integers, and $\mathcal F$ a graph class that contains, for each $m\in S$, a graph $F_m$ such that for every graph $X$
--   $$\hom(F_m,X)\equiv\hom(H,X)\pmod m.$$
--   Then $H\in\mathrm{Cl}(\mathcal F)$.
--
--   This turns modular homomorphism-count identities into exact dependence: it is the first half of the modular criterion (Corollary 7) used for the counterexamples.
--
--   Differences from the source:
--   - generalization: a graph class (closed under isomorphism) → any predicate $\mathcal F$ on simple graphs on finite types; reason: an isomorphism-closed class is such a predicate, so the statement specializes to the paper's
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Proposition 5, p.7 (PDF p.9), eq. (2)

import Mathlib
import Definitions.Def_RobersonCx_InCl

set_option autoImplicit false

namespace RobersonCx

/-- Proposition 5 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §3, p.7 (PDF p.9)). Let `H` be a graph, `S` an infinite set of positive integers, and
`𝓕` a graph class containing, for each `m ∈ S`, a graph `F_m` with `hom(F_m, X) ≡ hom(H, X) (mod m)` for every
graph `X` (eq. (2)). Then `H ∈ Cl(𝓕)`.

**Formalization Note** `𝓕` is any predicate on finite graphs (the paper's classes are isomorphism-closed, a
special case). Graphs `H`, `F_m`, `X` are simple graphs on finite types in `Type`. -/
theorem proposition_5 {W : Type} [Finite W] (H : SimpleGraph W) (S : Set ℕ) (hS : S.Infinite)
    (hpos : ∀ m ∈ S, 0 < m) (𝓕 : GraphClass)
    (hF : ∀ m ∈ S, ∃ (V : Type) (_ : Finite V) (F : SimpleGraph V), 𝓕 V F ∧
      ∀ (X : Type) [Finite X] (GX : SimpleGraph X), homCount F GX ≡ homCount H GX [MOD m]) :
    InCl 𝓕 H := by sorry

end RobersonCx
