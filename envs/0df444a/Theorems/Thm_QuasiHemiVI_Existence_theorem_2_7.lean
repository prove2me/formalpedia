-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_theorem_2_7
-- name    : QuasiHemiVI.Existence.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:36:16.452099+00:00
-- url     : https://prove2.me/theorems/70d78757-9461-4d64-90b3-3773b814f211
-- title:
--   Theorem 2.7 (Kluge) — fixed point of a multivalued map with sequentially weakly closed graph
-- statement:
--   Let $Z$ be a real reflexive Banach space and $C\subseteq Z$ nonempty, closed and convex. Let $\Psi:C\to2^C$ be a multivalued map such that
--
--   1. for every $u\in C$ the set $\Psi(u)$ is nonempty, closed and convex;
--   2. the graph of $\Psi$ is sequentially weakly closed;
--   3. $C$ is bounded, or $\Psi(C)=\bigcup_{u\in C}\Psi(u)$ is bounded.
--
--   Then $\Psi$ has a fixed point:
--
--   $$
--   \exists\,u\in C\quad\text{with}\quad u\in\Psi(u).
--   $$
--
--   The paper quotes this theorem from Kluge (reference [30]) and applies it to the variational selection $S$ to produce a solution of the quasi-hemivariational inequality.
--
--   **Formalization Note** $\Psi$ is a total function `Z → Set Z`; the hypotheses constrain it on $C$ only, including $\Psi(u)\subseteq C$.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1249, Theorem 2.7 (cited from [30], Kluge)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued

namespace QuasiHemiVI.Existence

/-- Theorem 2.7 (Kluge, cited as [30]), p. 1249: let `Z` be a reflexive Banach space and
`C ⊆ Z` nonempty, closed and convex; let `Ψ : C → 2^C` have nonempty, closed, convex values and a
sequentially weakly closed graph. If `C` is bounded or `Ψ(C)` is bounded, `Ψ` has a fixed point
in `C`. -/
theorem theorem_2_7 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (hZ : IsReflexive Z) (C : Set Z) (hCne : C.Nonempty) (hCcl : IsClosed C)
    (hCcv : Convex ℝ C) (Ψ : Z → Set Z)
    (hΨ : ∀ u ∈ C, Ψ u ⊆ C ∧ (Ψ u).Nonempty ∧ IsClosed (Ψ u) ∧ Convex ℝ (Ψ u))
    (hgr : SeqWeaklyClosedGraphOn C Ψ)
    (hbd : Bornology.IsBounded C ∨ Bornology.IsBounded (⋃ u ∈ C, Ψ u)) :
    ∃ u ∈ C, u ∈ Ψ u := by sorry

end QuasiHemiVI.Existence
