-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz10
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:35:38.462976+00:00
-- url     : https://prove2.me/theorems/495109ef-4078-465c-800e-27957f29b7d2
-- title:
--   Satz 10 — $(S') = (S)$, and the extreme solutions of $\Sigma$ are points of $S$ up to a positive factor
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, whose region $(S)$ contains an inner point $\xi^0$, i.e. $(a\xi^0) > 0$ for every $a \in S$ (the hypotheses of Satz 9, kept for the rest of §3). Let $\Sigma$ be the dual system, whose inequalities are all extreme solutions of $S$, and let $a', b', \dots$ be the extreme solutions of $\Sigma$. Then:
--
--   1. the region $(S')$ defined by the inequalities $S' : (a'\xi) \ge 0, (b'\xi) \ge 0, \dots$ is
--   $$(S') = (S);$$
--   2. each $a'$ is a selection among the points of $S$ up to a positive factor: $a' = \rho\,a$ for some $a \in S$ and $\rho > 0$.
--
--   Satz 10 is the first half of the complete dualization: going from $S$ to $\Sigma$ and back to $S'$ recovers the original region, and $S'$ consists of points of $S$.
--
--   (Weyl: "Satz 10. Der durch die zu Σ dualen Ungleichungen S′ : (a′ξ) ≧ 0, (b′ξ) ≧ 0, ⋯ definierte Bereich (S′) ist mit (S) identisch. Die Punkte a′, b′, ⋯ sind eine Auswahl unter den Punkten a, b, ⋯ von S.")
--
--   **Formalization Note** $\Sigma$ and $S'$ contain every positive multiple of their rays, so they are infinite sets of inequalities (definition `DualSystems`). The selection is up to a positive factor, as in Weyl's proof ("bis auf einen positiven Proportionalitätsfaktor"); literally $a' \in S$ would be false, since $2a'$ is an extreme solution of $\Sigma$ whenever $a'$ is.
--
--   Differences from the source:
--   - encoding: the hypotheses of Satz 9, "die für den Rest dieses Paragraphen beibehalten werden" (p. 299) → explicit hypotheses Shared.NonDegenerate S and ∃ ξ₀, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀; reason: standing assumptions of the rest of §3 made explicit; they change no instance of the source's claim
--   - reading: the points a′, b′, ⋯ are a selection among the points a, b, ⋯ of S → every a′ ∈ sPrimeSet S equals ρ • a for some a ∈ S and ρ > 0; reason: points on the same ray are not distinguished (p. 290–291), and the proof says "bis auf einen positiven Proportionalitätsfaktor" (p. 300); literal membership a′ ∈ S fails for 2a′
--   - encoding: the extreme solutions a′, b′, ⋯ of Σ and the inequalities α, β, ⋯ of Σ → the sets sigmaSet S and sPrimeSet S of all extreme solutions, every positive multiple included; reason: no representatives are chosen; positive multiples give the same inequality, so the regions are unchanged
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 300, Satz 10, with the standing hypotheses of p. 299 (§3 III)

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 10, under the hypotheses of Satz 9 kept for the rest of §3
(`S` non-degenerate, `(S)` with an inner point `ξ⁰`). Let `a′, b′, ⋯` be the extreme solutions
of the dual system `Σ` (`sPrimeSet S`). Then
1. the region `(S′)` defined by the inequalities `a′ ⬝ᵥ ξ ≥ 0` equals `(S)`, and
2. the points `a′, b′, ⋯` are a selection among the points of `S`, up to a positive factor
   (as the proof says, "bis auf einen positiven Proportionalitätsfaktor"). -/
theorem satz10 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    regionOf (sPrimeSet S) = solutionRegion S ∧
      ∀ a' ∈ sPrimeSet S, ∃ a ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ a' = ρ • a := by sorry

end WeylPolyhedra.Polyhedron.Supplement
