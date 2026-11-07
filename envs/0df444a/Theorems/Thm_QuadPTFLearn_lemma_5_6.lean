-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_5_6
-- name    : QuadPTFLearn.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:57.970033+00:00
-- url     : https://prove2.me/theorems/cb440fb4-ebc2-43cf-86c6-9aa0cfd9b72b
-- title:
--   Lemma 5.6, p.33 — boundary identity $\mathbb E_z[f_w(z)M_vp(zv+w)]=\sum_{s\in S_w}\Delta f_w(s)p(sv+w)\phi(s)$
-- statement:
--   Let $f:\mathbb R^d\to\{0,1\}$ be a Boolean function and $v\in S^{d-1}$. Write $x=zv+w$ with $z=v\cdot x$, $w=\mathrm{proj}_{v^\perp}(x)$, and $f_w(z)=f(zv+w)$. If $f_w$ is a step function with a finite set $S_w$ of jump points, then for every polynomial $p:\mathbb R^d\to\mathbb R$,
--   $$\mathbb E_{z\sim N(0,1)}\big[f_w(z)\,M_vp(zv+w)\big]=\sum_{s\in S_w}\Delta f_w(s)\,p(sv+w)\,\phi(s),$$
--   where $\Delta f_w(s)$ is the jump of $f_w$ at $s$ and $M_vp=(x\cdot v)p-\partial_vp$.
--
--   The correlation of $f$ with $M_vp$ along a line is the signed sum of the values of $p$ at the decision boundary, which is how certificates are built in Section 5.
--
--   Differences from the source:
--   - generalization: S_w the set of jump points of the step function f_w → any finite set S such that f_w is constant on every closed interval avoiding S; reason: at a point of S that is not a jump the jump Δf_w is 0, so taking S = S_w gives the source's identity
--   - reading: E[f_w M_v p(zv + w)] = E[f′_w(z) p(zv + w)] with the distributional derivative f′_w → not stated separately; reason: with f′_w the distributional derivative, this display is its definition applied to the test function p(zv + w)ϕ(z); its content for step functions is the identity stated
--   - encoding: Δf_w(s) = lim_{τ→0⁺} f_w(s+τ) − lim_{τ→0⁺} f_w(s−τ) → limUnder of the right minus the left neighbourhood filter; reason: the one-sided limits exist for a step function
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 5.6, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 5.6, p.33 (PDF p.35), the "in particular" identity.

Let `f : ℝᵈ → {0, 1}` be Boolean, `v` a unit vector, `w ⊥ v`, `f_w(z) = f(zv + w)`. If `f_w` is a
step function with the finite set of jump points `S_w`, then for every polynomial `p`,
`E_{z∼N(0,1)}[f_w(z) M_v p(zv + w)] = Σ_{s∈S_w} Δf_w(s) p(sv + w) ϕ(s)`.

**Formalization Note.** The set `S` may be any finite set off which `f_w` is locally constant
(its jump points lie in `S`; at a point of `S` that is not a jump, `Δf_w = 0`). The page's first
display, `E[f_w M_v p] = E[f′_w p]` with the distributional derivative `f′_w`, is the definition of
that derivative applied to the test function `p(zv + w)ϕ(z)` and is not posed separately. -/
theorem lemma_5_6 {d : ℕ} (f : Pt d → ℝ) (hf : IsBoolean f) (v : Pt d) (hv : ‖v‖ = 1)
    (w : Pt d) (hw : ⟪v, w⟫ = 0) (p : Poly d) (S : Finset ℝ) (hS : IsStepOff (layer f v w) S) :
    ∫ z, layer f v w z * peval (boundaryOp v p) (z • v + w) ∂N01 =
      ∑ s ∈ S, jump (layer f v w) s * peval p (s • v + w) * phi s := by sorry

end QuadPTFLearn
