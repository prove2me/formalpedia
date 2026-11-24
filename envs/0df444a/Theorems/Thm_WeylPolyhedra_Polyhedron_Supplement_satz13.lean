-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz13
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:38:08.969734+00:00
-- url     : https://prove2.me/theorems/464ea9dc-c200-4bf0-8a17-7330e9734982
-- title:
--   Satz 13 (corrected: pyramids of arbitrary finite point systems) — the intersection of two convex pyramids is a convex pyramid
-- statement:
--   Call the set of nonnegative linear combinations of a finite point system $T \subseteq \mathbb{R}^n$,
--   $$\operatorname{cone} T = \{\lambda a + \mu b + \dots : a, b, \dots \in T,\ \lambda, \mu, \dots \ge 0\},$$
--   the **convex pyramid** of $T$. For any two finite point systems $S_1, S_2 \subseteq \mathbb{R}^n$ there is a finite point system $T \subseteq \mathbb{R}^n$ with
--   $$\operatorname{cone} S_1 \cap \operatorname{cone} S_2 = \operatorname{cone} T.$$
--
--   Satz 13 is the first consequence Weyl draws from the complete dualization: a pyramid can be given equally by finitely many points or by finitely many inequalities, and the two descriptions are exchanged freely.
--
--   (Weyl: "Satz 13. Der Durchschnitt zweier konvexen Pyramiden ist wiederum eine konvexe Pyramide.")
--
--   **Formalization Note** On p. 291 the convex pyramid is introduced for a *non-degenerate* finite system. Read literally with that definition Satz 13 is false: in $\mathbb{R}^2$, $\operatorname{cone}\{e_1, e_2\} \cap \operatorname{cone}\{e_1, -e_2\} = \operatorname{cone}\{e_1\}$, which lies in a line and so is the pyramid of no non-degenerate system. Weyl's proof unites the two systems of supporting inequalities and takes the extreme solutions of the united system, which may be degenerate. His remark on p. 300 treats a pyramid as given by finitely many points or finitely many supports. The statement therefore uses pyramids of arbitrary finite systems, for $S_1$, $S_2$ and $T$.
--
--   Differences from the source:
--   - correction: the intersection is a convex pyramid, i.e. (p. 291) the pyramid of a non-degenerate finite system → ∃ T : Finset, with no non-degeneracy required of T; reason: literally false: cone{e₁, e₂} ∩ cone{e₁, −e₂} = cone{e₁} in ℝ² is not full-dimensional; Weyl's proof (p. 301) takes the extreme solutions of the united, possibly degenerate, system, and p. 300 treats pyramids as given by any finitely many points or supports
--   - generalization: two convex pyramids, i.e. pyramids of non-degenerate finite systems S₁, S₂ → arbitrary finite S₁, S₂; reason: after the correction the conclusion is the pyramid of an arbitrary finite system, and the same reading applies to the inputs; the source's case of non-degenerate S₁, S₂ is the special case
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 301, Satz 13 (§3 V), with the definition of the convex pyramid on p. 291 and the remark on p. 300

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 V, p. 301, Satz 13: the intersection of two convex pyramids is again a
convex pyramid. A convex pyramid is read as the set of points representable (nonnegative linear
combinations) by a finite point system — by p. 300 equivalently the region of finitely many
homogeneous inequalities. For any finite `S₁, S₂ ⊆ ℝⁿ` there is a finite `T ⊆ ℝⁿ` whose
pyramid is the intersection of the pyramids of `S₁` and `S₂`. No non-degeneracy is required of
`S₁, S₂` or `T` (with it the statement would be false: see the natural-language statement). -/
theorem satz13 {n : ℕ} (S₁ S₂ : Finset (Fin n → ℝ)) :
    ∃ T : Finset (Fin n → ℝ),
      {x | Shared.Representable S₁ x} ∩ {x | Shared.Representable S₂ x} =
        {x | Shared.Representable T x} := by sorry

end WeylPolyhedra.Polyhedron.Supplement
