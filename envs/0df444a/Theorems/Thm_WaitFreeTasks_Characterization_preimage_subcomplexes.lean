-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_preimage_subcomplexes
-- name    : WaitFreeTasks.Characterization.preimage_subcomplexes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:04.299388+00:00
-- url     : https://prove2.me/theorems/75af3cbd-f222-48e5-9101-763387d57655
-- title:
--   Proposition 5 — Preimage subcomplexes cover the refinement
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   Let $K$ be any geometric subdivision of $D$. For an output simplex $\Sigma$, define $\operatorname{pre}_f^K(\Sigma)=\{\sigma\in K:f(|\sigma|)\subseteq|\Sigma|\}$. Then all three assertions hold:
--
--   $$\operatorname{pre}_f^K(\Sigma)\text{ is a subcomplex of }K\quad(\Sigma\in O),$$
--   $$\forall\sigma\in K,\ \exists\Sigma\in O:\ f(|\sigma|)\subseteq|\Sigma|,$$
--   $$K=\bigcup_{\Sigma\in O}\operatorname{pre}_f^K(\Sigma).$$
--
--   Subcomplex includes closure under every nonempty face. These properties organize the refinement by output simplices without changing $f$.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 11 (PDF p. 13), Proposition 5

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Proposition 5** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 11, PDF p. 13). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
For every subdivision `K` of `div(I)`:
1. for every `Σ ∈ O`, `pre^K_f(Σ)` is a subcomplex of `K`;
2. for every simplex `σ' ∈ K` there is `Σ_{σ'} ∈ O` with `f(|σ'|) ⊆ |Σ_{σ'}|`;
3. `K = ⋃_{Σ ∈ O} pre^K_f(Σ)`. -/
theorem preimage_subcomplexes {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (K : GCx (VI → ℝ)) (hK : Refines K D) :
    (∀ S ∈ T.O.faces, pre K.faces f S ⊆ K.faces ∧
      ∀ σ ∈ pre K.faces f S, ∀ σ' : Finset (VI → ℝ), σ'.Nonempty → σ' ⊆ σ →
        σ' ∈ pre K.faces f S) ∧
    (∀ σ' ∈ K.faces, ∃ S ∈ T.O.faces, f '' gs σ' ⊆ face S) ∧
    K.faces = T.O.faces.biUnion (pre K.faces f) := by sorry

end WaitFreeTasks.Characterization
