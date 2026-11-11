-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_shatter_no_violations
-- name    : WaitFreeTasks.Characterization.shatter_no_violations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:59.580133+00:00
-- url     : https://prove2.me/theorems/389eb181-bb52-4d59-9fc8-49806e33cbcb
-- title:
--   Proposition 8 — Shattering creates no violated edge
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   Let $K$ refine $D$, fix $\Sigma\in O$ with colors $c_0<\cdots<c_d$, and let $d'\ge1$. Suppose $\operatorname{pre}_f^K(\Sigma)$ has no shallow simplex of dimension greater than $d'$. Shatter a shallow $d'$-simplex $\sigma$ of this preimage at any relative interior point $p$, setting its new color to $c_{d'}$ and retaining old colors. Put $K^+=\operatorname{ste}(K,\sigma)$ and denote the new coloring by $\operatorname{col}^+$. Then
--
--   $$e\in\operatorname{pre}_f^{K^+}(\Sigma),\quad e\text{ violated under }\operatorname{col}^+\quad\Longrightarrow\quad e\in K.$$
--
--   All newly introduced faces contain the new vertex; hence this says that no new violated edge is created. The index $c_{d'}$ is explicitly required to exist, as in this subphase of the procedure.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - generalization: K and col are the subdivision and coloring maintained by the Section 4.2 procedure at the moment a shallow d'-simplex is shattered (d' = d, ..., 1) → any geometric refinement K of div(I) with any coloring col, any d' >= 1; reason: the source's proof uses only the stated hypotheses (no shallow simplex above d', σ shallow, Lemma 6, linearity of f on simplices of K), and every procedure state is such a refinement with such a coloring
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 13 (PDF p. 15), Proposition 8

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Proposition 8** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 13, PDF p. 15). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `K` be a subdivision of `div(I)` with colouring `col`, `Σ ∈ O` with colours
`c_0 < ⋯ < c_d`, and `d' ≥ 1`. Assume `pre^K_f(Σ)` contains no shallow simplex of dimension larger
than `d'`, and shatter a shallow `d'`-simplex `σ ∈ pre^K_f(Σ)`: `K⁺ = ste(K, σ)` with new vertex
`p` in the interior of `|σ|`, coloured `c_{d'}` (old vertices keep their colours).
Then no new violated edges are created in `pre^{K⁺}_f(Σ)`: every violated edge of it is an edge
of `K`. -/
theorem shatter_no_violations {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (K : GCx (VI → ℝ)) (hK : Refines K D) (col : (VI → ℝ) → Fin n)
    (S : Finset VO) (hS : S ∈ T.O.faces) (d' : ℕ) (hd' : 1 ≤ d')
    (hno : ∀ ρ ∈ pre K.faces f S, IsShallow T col S ρ → ρ.card ≤ d' + 1)
    (σ : Finset (VI → ℝ)) (hσ : σ ∈ pre K.faces f S) (hσd : σ.card = d' + 1)
    (hsh : IsShallow T col S σ) (p : VI → ℝ) (hp : p ∈ openSimplex σ)
    (c : Fin n) (hc : colorAt T S d' = some c) :
    ∀ e ∈ pre (stellar K.faces σ p) f S, IsViolated (Function.update col p c) e →
      e ∈ K.faces := by sorry

end WaitFreeTasks.Characterization
