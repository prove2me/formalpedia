-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_9_5
-- name    : QuadPTFLearn.lemma_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:27.997401+00:00
-- url     : https://prove2.me/theorems/d6239f6c-ebdf-440b-95b7-eac439d2a43c
-- title:
--   Lemma 9.5, p.90 — the adjoint identity $\mathbb E[p\,d_vF]=\mathbb E[F\,T_vp]$
-- statement:
--   Let $v=(b,L,A)$ be a residual coefficient direction and $p$ a polynomial. Define
--   $$T_vp=p\,N_v(z,w)-(b+L^\top z+2Aw)^\top\nabla_wp+\mathrm{tr}(A\nabla_w^2p),\qquad N_v(z,w)=(b+L^\top z)^\top w+w^\top Aw-\mathrm{tr}(A).$$
--   Then for every sufficiently smooth function $F$,
--   $$\mathbb E_{z,w\sim N(0,I)}[p\,d_vF]=\mathbb E_{z,w\sim N(0,I)}[F\,T_vp].$$
--
--   The identity lets the algorithm estimate the bilinear form $\mathbb E[p\,d_vF]$ from labels alone, by replacing the derivative of the unknown target with a polynomial weight.
--
--   **Formalization Note** "Sufficiently smooth" is taken as: $F$ is $C^2$ and $|F|$, $\|DF\|$, $\|D^2F\|$ grow at most polynomially. Here $z=\mathrm{proj}_Vx$, $w=\mathrm{proj}_{V^\perp}x$ with $x\sim N(0,I_d)$.
--
--   Differences from the source:
--   - reading: for every sufficiently smooth function F → F of class C² with |F|, ‖DF‖, ‖D²F‖ ≤ K(1 + ‖x‖)^m; reason: the two Gaussian integrations by parts of the proof need exactly this; it contains every polynomial and every C² function with bounded derivatives
--   - reading: The identity also holds for bounded measurable F when d_vF is interpreted weakly → not stated; reason: for such F the weak action of d_v on polynomial test functions is defined by this identity, so the sentence asserts nothing beyond it
--   - encoding: (b, L, A) with b ∈ V⊥, L : V⊥ → V, A symmetric on V⊥; ∇_w, ∇²_w → b ∈ ℝᵈ and d × d matrices L, A constrained to vanish on V and map V⊥ into V and V⊥; full gradient and Hessian; reason: with this representation (b + Lᵀz)·∇F = (b + Lᵀz)·∇_wF and tr(A∇²F) = tr(A∇²_wF)
--   - encoding: z ∈ V, w ∈ V⊥ independent standard Gaussian vectors; E_{z,w∼N(0,I)} → z = proj_V x, w = proj_{V⊥} x with x ∼ N(0, I_d); reason: the two projections of a standard Gaussian are independent standard Gaussians on V and V⊥
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 9.5, p.90 (PDF p.92)

import Mathlib
import Definitions.Def_QuadPTFLearn_Residual

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 9.5, p.90 (PDF p.92).

Let `v = (b, L, A)` be a residual coefficient direction and `p` a polynomial. With
`T_v p = p N_v(z, w) − (b + Lᵀz + 2Aw)ᵀ ∇_w p + tr(A ∇²_w p)` and
`N_v(z, w) = (b + Lᵀz)ᵀ w + wᵀ A w − tr(A)`, for every sufficiently smooth function `F`,
`E_{z,w∼N(0,I)}[p d_v F] = E_{z,w∼N(0,I)}[F T_v p]`.

**Formalization Note.** "Sufficiently smooth" is read as `C²` with `F`, `DF` and `D²F` of
polynomial growth. The page's last sentence ("The identity also holds for bounded measurable `F`
when `d_v F` is interpreted weakly") is the definition of the weak action of `d_v` by this
identity and is not a separate claim. `z = proj_V x` and `w = proj_{V⊥} x` with
`x ∼ N(0, I_d)`. -/
theorem lemma_9_5 {d : ℕ} (V : Submodule ℝ (Pt d)) (v : ResDir d) (hv : IsResDir V v)
    (p : Poly d) (F : Pt d → ℝ) (hF : ContDiff ℝ 2 F)
    (hgrowth : ∃ K : ℝ, ∃ m : ℕ, ∀ x, |F x| ≤ K * (1 + ‖x‖) ^ m ∧
      ‖fderiv ℝ F x‖ ≤ K * (1 + ‖x‖) ^ m ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ K * (1 + ‖x‖) ^ m) :
    ∫ x, peval p x * dRes V v F x ∂gauss d = ∫ x, F x * resAdj V v p x ∂gauss d := by sorry

end QuadPTFLearn
