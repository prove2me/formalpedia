-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_5_11
-- name    : QuadPTFLearn.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:59.109045+00:00
-- url     : https://prove2.me/theorems/d5d40fb2-e2ed-4aeb-9b00-ccd9f34cdc67
-- title:
--   Lemma 5.11, p.35 — certificate $Q_v=\partial_v\prod_iq_i$ with $\mathbb E[fM_vQ_v]\ge\eta_d\eta_c^{k-1}\alpha$ for generic jump points
-- statement:
--   **Certificate polynomials for generic intersections of PTFs.** Let $v\in S^{d-1}$, $w=\mathrm{proj}_{v^\perp}x$, and $f(x)=g(w)\,1\{p_1(x)\ge t_1,\dots,p_k(x)\ge t_k\}$, where each $p_i$ is a polynomial of degree at most two with $\mathbb E[p_i]=0$, $\mathrm{Var}[p_i]=1$, $t_i\in\mathbb R$, and $g:v^\perp\to\{0,1\}$. Let $q_i=p_i-t_i$ and $Q_v=\partial_v\big(\prod_{i=1}^kq_i\big)$. For $\eta_d,\eta_c\in(0,1)$ and $w\perp v$ let $G_w(\eta_d,\eta_c)\subseteq S_w$ be a set of jump points of $f_w$ such that for each $s\in G_w(\eta_d,\eta_c)$ there is $i$ with $|(q_i^{(w)})'(s)|\ge\eta_d$ and $q_j^{(w)}(s)\ge\eta_c$ for every $j\ne i$, where $q^{(w)}(s)=q(sv+w)$. If $\mathbb E_{w\sim N(0,I)}\big[\sum_{s\in G_w(\eta_d,\eta_c)}\phi(s)\big]\ge\alpha$, then
--   $$\mathbb E_{x\sim N(0,I)}\big[f(x)\,M_vQ_v(x)\big]\ge\eta_d\,\eta_c^{k-1}\alpha .$$
--
--   When enough boundary mass sits at well-separated simple roots, the derivative of the product of the defining polynomials is a certificate.
--
--   Differences from the source:
--   - generalization: G_w(η_d, η_c) ⊆ S_w the set of jump points with the stated property (Definition 5.10, item 1) → any family of sets G_w ⊆ S_w (w ⊥ v) whose points have the stated property; reason: the set of Definition 5.10 is one such family, so the statement specializes to the source's
--   - encoding: g(w) : v⊥ → {0,1}; E_w; (q_i^{(w)})′ → a measurable {0,1}-valued g at x − ⟪v,x⟫v; w = proj_{v⊥}x, the expectation of the nonnegative sum as a lower Lebesgue integral; the derivative of s ↦ q_i(sv + w); reason: the same objects; measurability makes the expectation defined
--   - encoding: i ∈ [k]; α → 1 ≤ k; α any real number; reason: [k] for k ∈ ℤ₊; the source puts no condition on α
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 5.11 (Certificate Polynomials for Generic Intersections of PTFs), p.35 (PDF p.37); Definition 5.10, pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 5.11 (Certificate polynomials for generic intersections of PTFs), p.35 (PDF p.37).

Let `f(x) = g(w) 1{p₁(x) ≥ t₁, …, p_k(x) ≥ t_k}` with `deg pᵢ ≤ 2`, `E[pᵢ] = 0`, `Var[pᵢ] = 1`,
`tᵢ ∈ ℝ`, `g : v⊥ → {0, 1}`, `v` a unit vector. Let `qᵢ = pᵢ − tᵢ` and `Q_v = ∂_v(∏ᵢ qᵢ)`. For
`η_d, η_c ∈ (0, 1)` and `w ⊥ v` let `G_w(η_d, η_c) ⊆ S_w` be such that for each `s ∈ G_w` there is
`i` with `|(qᵢ^{(w)})′(s)| ≥ η_d` and `qⱼ^{(w)}(s) ≥ η_c` for every `j ≠ i`. If
`E_{w∼N(0,I)}[Σ_{s∈G_w} ϕ(s)] ≥ α`, then `E_{x∼N(0,I)}[f(x) M_v Q_v(x)] ≥ η_d η_c^{k−1} α`.

**Formalization Note.** The statement holds for every family of sets `G_w` with the stated
property (the largest one, Definition 5.10 item 1, is a special case). `qᵢ^{(w)}(s) = qᵢ(sv + w)`;
`w = proj_{v⊥} x`; `g` is measurable. -/
theorem lemma_5_11 {d k : ℕ} (hk : 1 ≤ k) (p : Fin k → Poly d)
    (hp : ∀ i, (p i).totalDegree ≤ 2 ∧ mean (peval (p i)) = 0 ∧ var (peval (p i)) = 1)
    (t : Fin k → ℝ) (g : Pt d → ℝ) (hgm : Measurable g) (hgb : IsBoolean g)
    (v : Pt d) (hv : ‖v‖ = 1) (ηd ηc : ℝ) (hηd : 0 < ηd ∧ ηd < 1) (hηc : 0 < ηc ∧ ηc < 1)
    (Gw : Pt d → Set ℝ)
    (hG : ∀ w : Pt d, ⟪v, w⟫ = 0 →
      Gw w ⊆ jumpSet (layer (fun x => g (perp v x) *
        (if ∀ i, t i ≤ peval (p i) x then (1 : ℝ) else 0)) v w) ∧
      ∀ s ∈ Gw w, ∃ i, ηd ≤ |deriv (fun r => peval (p i - MvPolynomial.C (t i)) (r • v + w)) s| ∧
        ∀ j, j ≠ i → ηc ≤ peval (p j - MvPolynomial.C (t j)) (s • v + w))
    (α : ℝ) (hα : ENNReal.ofReal α ≤ ∫⁻ x, ∑' s : Gw (perp v x), ENNReal.ofReal (phi s) ∂gauss d) :
    ηd * ηc ^ (k - 1) * α ≤
      ∫ x, g (perp v x) * (if ∀ i, t i ≤ peval (p i) x then (1 : ℝ) else 0) *
        peval (boundaryOp v (dirDeriv v (∏ i, (p i - MvPolynomial.C (t i))))) x ∂gauss d := by sorry

end QuadPTFLearn
