-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_proper_iff_no_shallow
-- name    : WaitFreeTasks.Characterization.proper_iff_no_shallow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:13.214538+00:00
-- url     : https://prove2.me/theorems/f65450e3-ab72-4109-a2f0-e11dc1a33d61
-- title:
--   Claim 7 — Proper coloring is equivalent to no shallow face
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   Let $K$ refine $D$ and let $\operatorname{col}_K$ be a coloring. Fix $\Sigma\in O$ with colors $c_0<\cdots<c_d$. Assume every vertex of $\operatorname{pre}_f^K(\Sigma)$ has a color of $\Sigma$, and its only violated edges have both endpoints colored $c_0$. For every $\sigma\in\operatorname{pre}_f^K(\Sigma)$,
--
--   $$\operatorname{col}_K|_\sigma\text{ is injective}\quad\Longleftrightarrow\quad\text{no nonempty face of }\sigma\text{ is shallow}.$$
--
--   A nonempty face $\rho$ is shallow when every vertex color is less than $c_{\dim\rho}$. An edge is violated when its endpoints share a color. This criterion relates the two obstructions handled in the refinement.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 11 (PDF p. 13), Claim 7

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Claim 7** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 11, PDF p. 13). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `K` be a subdivision of `div(I)` with a colouring `col`, and let `Σ ∈ O` have colours
`c_0 < ⋯ < c_d`. Suppose every vertex of `pre^K_f(Σ)` has a colour in `{c_0, …, c_d}` and the
only violated edges of `pre^K_f(Σ)` are coloured `(c_0, c_0)`. Then a simplex `σ ∈ pre^K_f(Σ)` is
properly coloured iff no nonempty face `σ' ⊆ σ` is shallow. -/
theorem proper_iff_no_shallow {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (K : GCx (VI → ℝ)) (hK : Refines K D) (col : (VI → ℝ) → Fin n)
    (S : Finset VO) (hS : S ∈ T.O.faces)
    (hcolors : ∀ v ∈ verts (pre K.faces f S), col v ∈ S.image T.idO)
    (hviol : ∀ e ∈ pre K.faces f S, IsViolated col e → ∀ v ∈ e, colorAt T S 0 = some (col v)) :
    ∀ σ ∈ pre K.faces f S, (Set.InjOn col (σ : Set (VI → ℝ)) ↔
      ∀ σ' : Finset (VI → ℝ), σ'.Nonempty → σ' ⊆ σ → ¬ IsShallow T col S σ') := by sorry

end WaitFreeTasks.Characterization
