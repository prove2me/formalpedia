-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz11
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:37:07.334417+00:00
-- url     : https://prove2.me/theorems/1be779b9-8937-48b7-8825-dbe1ae12742a
-- title:
--   Satz 11 — $S'$ and $\Sigma$ are mutually dual: the extreme solutions of $S'$ are those of $S$
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, whose region $(S)$ contains an inner point (the hypotheses of Satz 9, kept for the rest of §3). Let $\Sigma$ be the set of extreme solutions of $S$ and $S'$ the set of extreme solutions of $\Sigma$. The systems $S'$ and $\Sigma$ are mutually dual. $S'$ is the dual system of $\Sigma$ by definition; conversely, for every $\xi \in \mathbb{R}^n$,
--   $$\xi \text{ is an extreme solution of } S' \iff \xi \text{ is an extreme solution of } S,$$
--   so $\Sigma$ is the dual system of $S'$.
--
--   Satz 11 completes the dualization begun in Satz 10: from $S'$ onward, passing to the dual system alternates between $S'$ and $\Sigma$.
--
--   (Weyl: "… sondern die extremen Lösungen von S′ sind mit den extremen Lösungen von S identisch: Satz 11. Die Systeme von Ungleichungen S′ und Σ sind wechselseitig zueinander dual.")
--
--   **Formalization Note** "Mutually dual" is stated as the identity of the extreme solutions of $S'$ and of $S$, as the sentence before Satz 11 explains it. The extreme solutions of the infinite set $S'$ use the definition `DualSystems`.
--
--   Differences from the source:
--   - encoding: the hypotheses of Satz 9, "die für den Rest dieses Paragraphen beibehalten werden" (p. 299) → explicit hypotheses Shared.NonDegenerate S and ∃ ξ₀, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀; reason: standing assumptions of the rest of §3 made explicit; they change no instance of the source's claim
--   - reading: the systems S′ and Σ are mutually dual → for every ξ, ξ is an extreme solution of sPrimeSet S iff IsExtremeSolution S ξ; reason: the sentence introducing Satz 11 says exactly this; S′ being the dual of Σ is its definition
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 300, Satz 11, with the standing hypotheses of p. 299 (§3 III)

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 11, under the hypotheses of Satz 9 kept for the rest of §3
(`S` non-degenerate, `(S)` with an inner point `ξ⁰`): the systems `S′` and `Σ` are mutually
dual. `S′` consists of the extreme solutions of `Σ` by definition (`sPrimeSet S`); the content
is the converse, stated in the sentence before Satz 11: the extreme solutions of `S′` are exactly
the extreme solutions of `S`, i.e. the inequalities of `Σ`. -/
theorem satz11 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ ξ : Fin n → ℝ, IsExtremeSolutionOf (sPrimeSet S) ξ ↔ IsExtremeSolution S ξ := by sorry

end WeylPolyhedra.Polyhedron.Supplement
