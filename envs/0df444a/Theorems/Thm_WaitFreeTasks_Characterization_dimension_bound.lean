-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_dimension_bound
-- name    : WaitFreeTasks.Characterization.dimension_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:54.949554+00:00
-- url     : https://prove2.me/theorems/4a760365-a76d-4385-8ce4-676bb689c775
-- title:
--   Lemma 6 — Finite fibers prevent dimension collapse
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   Let $K$ be a geometric subdivision of $D$, $\Sigma\in O$, and $\sigma\in\operatorname{pre}_f^K(\Sigma)$. Then
--
--   $$\dim\sigma\le\dim\Sigma.$$
--
--   Both simplices are nonempty, so this is equivalently $|\sigma|\le|\Sigma|$ for their vertex cardinalities. The bound ensures that the ordered output color indexed by the dimension of $\sigma$ exists. Appendix C supplies the source proof.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: dimension inequality for nonempty simplices → vertex-cardinality inequality; reason: subtracting one on both nonzero cardinalities preserves the inequality
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 11 (PDF p. 13), Lemma 6; Appendix C, p. 33 (PDF p. 35)

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 6** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 11, PDF p. 13; proved in Appendix C, printed p. 33,
PDF p. 35). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
For every `Σ ∈ O` and every subdivision `K` of `div(I)`, every `σ ∈ pre^K_f(Σ)` satisfies
`dim σ ≤ dim Σ` (equivalently `|σ| ≤ |Σ|`). -/
theorem dimension_bound {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (K : GCx (VI → ℝ)) (hK : Refines K D) :
    ∀ S ∈ T.O.faces, ∀ σ ∈ pre K.faces f S, σ.card ≤ S.card := by sorry

end WaitFreeTasks.Characterization
