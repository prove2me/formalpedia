-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_theorem_5_6
-- name    : ProjSelfConcordant.ConicExt.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:27:22.824802+00:00
-- url     : https://prove2.me/theorems/d43ace73-0376-4a2b-b353-f29658004b3b
-- title:
--   Theorem 5.6, p. 15 (corrected: barrier on X, printed "on f") — for bounded X and X°, f∗ is a projectively self-concordant barrier on −X° and x ↦ p bijects Xᵒ onto int(−X°)
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set such that both $X$ and its polar $X^\circ=\{p\mid\langle x,p\rangle\le1\ \forall x\in X\}$ are bounded, and let $f$ be a projectively self-concordant barrier on $X$ with parameter $\gamma$. Then
--
--   1. the dual function $f_*(p)=-\min_{x\in X^o}\bigl(f(x)+\log(1+\langle x,p\rangle)\bigr)$ has domain exactly the interior of $-X^\circ$;
--   2. $-X^\circ$ is a regular convex set and $f_*$ is a projectively self-concordant barrier on $-X^\circ$ with the same parameter $\gamma$;
--   3. the map
--   $$x\mapsto p=-\frac{f'(x)}{1+\langle f'(x),x\rangle}$$
--   is a bijection between the interiors of $X$ and $-X^\circ$.
--
--   This is the symmetric duality between projectively self-concordant barriers on a set and on its negative polar.
--
--   **Formalization Note** The polar is the published `ConeLifts.Shared.polar` (one-sided, $\langle x,p\rangle\le1$), and $-X^\circ$ is its pointwise negation. "Defined at $p$" means membership in the domain of Definition 5.2. Being a barrier includes $C^3$ regularity, conditions (1) and (3) with parameter $\gamma$ on the interior of $-X^\circ$, and $f_*\to+\infty$ at every boundary point of $-X^\circ$.
--
--   Differences from the source:
--   - correction: "a projectively self-concordant barrier on f" → a projectively self-concordant barrier on X; reason: typo; Definition 5.2 and the two paragraphs before Theorem 5.6 (p. 15) take f to be a barrier on X, and "on f" has no other meaning
--   - reading: f∗ "is a projectively self-concordant barrier on −X°" → in addition the conclusion states that −X° is a regular convex set; reason: Definition 1.4 defines barriers only on regular convex sets, so the source's conclusion presupposes it
--   - reading: the parameter of the dual barrier is not named in the theorem → the same γ; reason: Corollary 5.5 (p. 15) gives the dual condition with the same parameter, and the proof of Theorem 5.6 only adds condition (2)
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
--   - reading: f∗ is defined on the whole interior of −X° → dualDomain X f = interior (−X°); reason: the paragraph immediately before Theorem 5.6 says the domain consists of the whole interior; Definition 5.2 supplies the reverse containment
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 15, Theorem 5.6 (with Definition 5.2, p. 13, and Corollary 5.5, p. 15)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality
import Definitions.Def_ConeLifts_Shared_polar

namespace ProjSelfConcordant.ConicExt.Supplement

open scoped Pointwise

/-- Theorem 5.6, p. 15: let `X` be a regular convex set such that both `X` and its polar `X°` are
bounded (`X° = {p | ⟨x, p⟩ ≤ 1 ∀ x ∈ X}`, the published
`ConeLifts.Shared.polar`), and let `f` be a projectively self-concordant barrier on `X` with parameter `γ`. Then the
dual domain is exactly the interior of `−X°` and is a projectively self-concordant
barrier on the regular convex set `−X°` with the same parameter `γ`, and the map
`x ↦ −f′(x)/(1 + ⟨f′(x), x⟩)` is a bijection between the interiors of `X` and `−X°`. -/
theorem theorem_5_6 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (hXb : Bornology.IsBounded X)
    (hPb : Bornology.IsBounded (ConeLifts.Shared.polar X)) (γ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ProjBarrier γ X f) :
    dualDomain X f = interior (-ConeLifts.Shared.polar X) ∧
    RegularConvexSet (-ConeLifts.Shared.polar X) ∧
    ProjBarrier γ (-ConeLifts.Shared.polar X) (fstar X f) ∧
    Set.BijOn (projGrad f) (interior X) (interior (-ConeLifts.Shared.polar X)) := by sorry

end ProjSelfConcordant.ConicExt.Supplement
