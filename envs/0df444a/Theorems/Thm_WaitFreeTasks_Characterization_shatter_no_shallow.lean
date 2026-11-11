-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_shatter_no_shallow
-- name    : WaitFreeTasks.Characterization.shatter_no_shallow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:09.26797+00:00
-- url     : https://prove2.me/theorems/3eaa47df-566b-4316-8ad0-4b2fc235010a
-- title:
--   Lemma 9 — Shattering creates no shallow simplex
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   Let $K$ refine $D$, fix $\Sigma\in O$ with colors $c_0<\cdots<c_d$, and let $d'\ge1$. Suppose its preimage has no shallow simplex of dimension greater than $d'$. Shatter a shallow $d'$-simplex $\sigma$ at any relative interior point $p$, color $p$ by $c_{d'}$, and leave old colors unchanged. For $K^+=\operatorname{ste}(K,\sigma)$ with this coloring,
--
--   $$\rho\in\operatorname{pre}_f^{K^+}(\Sigma),\quad\rho\text{ shallow}\quad\Longrightarrow\quad\rho\in K.$$
--
--   The conclusion applies to every dimension of newly created simplex. It is the source's preservation property for the descending shatter loops.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - generalization: K and col are the subdivision and coloring maintained by the Section 4.2 procedure at the moment a shallow d'-simplex is shattered (d' = d, ..., 1) → any geometric refinement K of div(I) with any coloring col, any d' >= 1; reason: the source's proof uses only the stated hypotheses (no shallow simplex above d', σ shallow, Lemma 6, linearity of f on simplices of K), and every procedure state is such a refinement with such a coloring
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 13 (PDF p. 15), Lemma 9

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 9** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 13, PDF p. 15). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `K` be a subdivision of `div(I)` with colouring `col`, `Σ ∈ O` with colours
`c_0 < ⋯ < c_d`, and `d' ≥ 1`. Assume `pre^K_f(Σ)` contains no shallow simplex of dimension larger
than `d'`, and shatter a shallow `d'`-simplex `σ ∈ pre^K_f(Σ)`: `K⁺ = ste(K, σ)` with new vertex
`p` in the interior of `|σ|`, coloured `c_{d'}` (old vertices keep their colours).
Then no new shallow simplices are created in `pre^{K⁺}_f(Σ)`: every shallow simplex of it is a
simplex of `K`. -/
theorem shatter_no_shallow {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (K : GCx (VI → ℝ)) (hK : Refines K D) (col : (VI → ℝ) → Fin n)
    (S : Finset VO) (hS : S ∈ T.O.faces) (d' : ℕ) (hd' : 1 ≤ d')
    (hno : ∀ ρ ∈ pre K.faces f S, IsShallow T col S ρ → ρ.card ≤ d' + 1)
    (σ : Finset (VI → ℝ)) (hσ : σ ∈ pre K.faces f S) (hσd : σ.card = d' + 1)
    (hsh : IsShallow T col S σ) (p : VI → ℝ) (hp : p ∈ openSimplex σ)
    (c : Fin n) (hc : colorAt T S d' = some c) :
    ∀ ρ ∈ pre (stellar K.faces σ p) f S, IsShallow T (Function.update col p c) S ρ →
      ρ ∈ K.faces := by sorry

end WaitFreeTasks.Characterization
