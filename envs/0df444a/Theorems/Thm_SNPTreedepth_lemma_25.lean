-- Prove2me | Theorems.Thm_SNPTreedepth_lemma_25
-- name    : SNPTreedepth.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:57.631697+00:00
-- url     : https://prove2.me/theorems/2099f63b-a7a7-4bd9-8b9f-a98628128ac8
-- title:
--   Lemma 25 — realizing vertices exist, are unique, have pattern $\mu$ and indices $\le p$
-- statement:
--   Let $R$ be a relational structure with treedepth decomposition $T$ of height $h$, let $p\ge1$, and let $\mu=(\varrho_1,\dots,\varrho_z)$ be the $p$-route pattern of $z$ elements of $R$, where $p\ge z\cdot h$. Then:
--
--   1. the realizing vertices of $\mu$ (the vertices $w_1,\dots,w_z$ with $\mathrm{rt}(w_m)=\varrho_m$) exist and are unique;
--   2. the $p$-route pattern of the realizing vertices is again $\mu$;
--   3. every entry $(t,i)$ of the $p$-route of a realizing vertex satisfies $i\le p$.
--
--   Realizing vertices are the canonical representatives of a pattern; they are what the extension theorem (Theorem 8) evaluates a $p$-pure solution on, and clause 3 is why they survive in $R^p$.
--
--   Differences from the source:
--   - encoding: μ the p-route pattern of z elements of R → μ = pattern(v) for a tuple v : Fin z → V(R); R finite, non-empty, totally ordered; reason: the pattern of some z elements, Definition 5
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Lemma 25, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_SNPTreedepth_ptype

set_option autoImplicit false

namespace SNPTreedepth

/-- **Lemma 25** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.23 (PDF p.24)): "Let R be a relational structure with treedepth
decomposition T of height h, p a positive integer, and μ = (ϱ₁, …, ϱ_z) be the p-route pattern of z
elements of R with p ≥ z · h. Then the realizing vertices of μ exist and are unique, and the p-route
pattern of the realizing vertices of μ is again μ. Moreover, every entry (t, i) in the p-route of a
realizing vertex satisfies i ≤ p."

**Formalization Note** `μ` is the `p`-route pattern of a tuple `v` of `z` elements; realizing
vertices are tuples `w` with `rt(w_m) = ϱ_m` for every `m` (Definition 24). `R` has a finite
non-empty domain with a total order. -/
theorem lemma_25 {σ : Signature} {V : Type*} [Fintype V] [LinearOrder V] [Nonempty V]
    (R : Structure σ V) (T : RootedForest V) (hT : IsTDDecomp R T) (p : ℕ) (hp : 1 ≤ p) {z : ℕ}
    (v : Fin z → V) (hz : z * T.height ≤ p) :
    (∃! w : Fin z → V, IsRealizing R T p (pattern R T p v) w) ∧
    ∀ w : Fin z → V, IsRealizing R T p (pattern R T p v) w →
      pattern R T p w = pattern R T p v ∧ ∀ m, ∀ e ∈ route R T p (w m), e.2 ≤ p := by sorry

end SNPTreedepth
