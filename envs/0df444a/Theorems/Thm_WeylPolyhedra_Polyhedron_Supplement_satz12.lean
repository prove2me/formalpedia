-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz12
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:37:44.296519+00:00
-- url     : https://prove2.me/theorems/d91df94e-148d-4e26-9c76-0be129d6c441
-- title:
--   Satz 12 — $n-1$ independent support planes through an extreme edge; $n-1$ independent extreme edges in an extreme support plane
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate point system such that some $\xi^0$ has $(a\xi^0) > 0$ for every $a \in S$ (the hypotheses of Satz 9, kept for the rest of §3). Consider the convex pyramid of $S$. Its **extreme edges** are the rays of the extreme solutions $a'$ of the dual system $\Sigma$; by Satz 10 they are points of $S$ up to a positive factor. Its **support planes** are the supports of $S$, i.e. the $\xi \neq 0$ with $(\xi s) \ge 0$ for all $s \in S$. Its **extreme support planes** are the extreme supports $\alpha$ of $S$. Then:
--
--   1. through every extreme edge $a'$ pass $n-1$ independent support planes: there are $n-1$ linearly independent supports $\xi$ of $S$ with $(\xi a') = 0$;
--   2. every extreme support plane $\alpha$ contains $n-1$ independent extreme edges: there are $n-1$ linearly independent extreme solutions $a'$ of $\Sigma$ with $(\alpha a') = 0$.
--
--   This is the incidence statement of Satz 10–11 read for pyramids, and it is the homogeneous form of the vertex–facet incidence of convex polyhedra in §4 I.
--
--   (Weyl: "Satz 12. Durch eine extreme Kante gehen n − 1 unabhängige Stützebenen, in einer extremen Stützebene liegen n − 1 unabhängige extreme Kanten.")
--
--   **Formalization Note** The paper does not define "extreme Kante". Satz 12 restates Satz 10–11 for convex pyramids ("Das Resultat mag man für die konvexen Pyramiden so aussprechen"), so the extreme edges are read as the extreme solutions of $\Sigma$. "Independent" means linear independence of the normal vectors $\xi$ (clause 1) and of the edge vectors $a'$ (clause 2) in $\mathbb{R}^n$.
--
--   Differences from the source:
--   - encoding: the hypotheses of Satz 9, "die für den Rest dieses Paragraphen beibehalten werden" (p. 299) → explicit hypotheses Shared.NonDegenerate S and ∃ ξ₀, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀; reason: standing assumptions of the rest of §3 made explicit; they change no instance of the source's claim
--   - reading: extreme Kante (extreme edge) of the convex pyramid, not defined in the paper → an extreme solution a′ of Σ (a′ ∈ sPrimeSet S); reason: Satz 12 restates Satz 10-11 "für die konvexen Pyramiden" (p. 300), and by Satz 10 these are the points of S that span edges of the pyramid
--   - reading: n − 1 unabhängige Stützebenen / extreme Kanten → a Finset of n − 1 linearly independent supports ξ (resp. extreme solutions a′ of Σ) orthogonal to a′ (resp. α); reason: a plane through the origin is given by its normal and an edge by its direction; Weyl's independence is linear independence in the homogeneous R_n, as in the definition of extreme supports (p. 291)
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 300, Satz 12, with the standing hypotheses of p. 299 (§3 III)

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 12, for the convex pyramid of `S`, under the hypotheses of
Satz 9 kept for the rest of §3 (`S` non-degenerate, `(S)` with an inner point `ξ⁰`). The extreme
edges of the pyramid are the rays of the extreme solutions `a′` of `Σ` (`sPrimeSet S`, by
Satz 10 a selection among the points of `S`); its support planes are the supports `ξ` of `S`
(`ξ ≠ 0`, `ξ ⬝ᵥ s ≥ 0` on `S`) and its extreme support planes the extreme supports of `S`.
1. Through every extreme edge `a′` pass `n - 1` linearly independent support planes.
2. Every extreme support plane `α` contains `n - 1` linearly independent extreme edges. -/
theorem satz12 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    (∀ a' ∈ sPrimeSet S, ∃ T : Finset (Fin n → ℝ), T.card = n - 1 ∧
        (∀ ξ ∈ T, Shared.IsSupport S ξ) ∧
        LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ ξ ∈ T, ξ ⬝ᵥ a' = 0) ∧
      (∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → ∃ T : Finset (Fin n → ℝ),
        T.card = n - 1 ∧ (↑T : Set (Fin n → ℝ)) ⊆ sPrimeSet S ∧
        LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a' ∈ T, α ⬝ᵥ a' = 0) := by sorry

end WeylPolyhedra.Polyhedron.Supplement
