-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_9_4
-- name    : QuadPTFLearn.lemma_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:37.318972+00:00
-- url     : https://prove2.me/theorems/62104a99-1f48-45dd-b8ea-bdd7471452de
-- title:
--   Lemma 9.4, p.89 — $|\mathbb E[p\,d_vF]-\sum_i\langle v,u_i\rangle\mathbb E[p\,\partial_i\psi]|\le C\tau(kD_1+k^2D_2)\|p\|_2$ under $(\tau,V)$-regularity
-- statement:
--   Let $V\subseteq\mathbb R^d$ and write $x=z+w$ with $z\in V$, $w\in V^\perp$ independent standard Gaussian vectors. For $i\in[k]$ let $q_i(z,w)=a_i(z)+N_{u_i}(z,w)$ with $u_i=(b_i,L_i,A_i)$ and $N_{u_i}(z,w)=(b_i+L_i^\top z)^\top w+w^\top A_iw-\mathrm{tr}(A_i)$, and suppose each $q_i$ is $(\tau,V)$-regular with $\mathrm{Var}(q_i)\le1$. Let $\psi:\mathbb R^k\to\mathbb R$ be $C^2$ with bounded first and second derivatives, $F=\psi(q_1,\dots,q_k)$ and $D_j(\psi)=\max_{i_1,\dots,i_j}\|\partial_{i_1}\cdots\partial_{i_j}\psi\|_\infty$ for $j\in\{1,2\}$. Then for every unit coefficient direction $v=(b,L,A)$ and every polynomial $p$,
--   $$\Big|\mathbb E[p\,d_vF]-\sum_{i=1}^k\langle v,u_i\rangle\,\mathbb E[p\,\partial_i\psi(q_1,\dots,q_k)]\Big|\le C\tau\big(kD_1(\psi)+k^2D_2(\psi)\big)\|p\|_2,$$
--   where $C>0$ is a universal constant.
--
--   Under regularity, $d_v$ acts on functions of the $q_i$ as a directional derivative in coefficient space, up to an error of order $\tau$.
--
--   **Formalization Note** "Unit" means $\|b\|^2+\|L\|_F^2+2\|A\|_F^2=1$ and $\langle v,u\rangle=b^\top b'+\langle L,L'\rangle_F+2\langle A,A'\rangle_F$, as in the proof. $D_1,D_2$ may be any bounds on the first and second partial derivatives.
--
--   Differences from the source:
--   - encoding: D_j(ψ) = max ∥∂_{i₁}⋯∂_{i_j}ψ∥_∞ → any D₁, D₂ bounding all first, resp. second, partial derivatives; reason: the statement for every bound is the statement for the least bound
--   - encoding: q_i(z, w) = a_i(z) + N_{u_i}(z, w), (τ, V)-regular → q_i a polynomial of degree ≤ 2 with q_i − N_{u_i} depending only on z; τ ∈ (0, 1); reason: Definition 3.1 defines regularity for degree-≤2 polynomials and τ ∈ (0, 1)
--   - encoding: unit coefficient direction v = (b, L, A); ⟨v, u_i⟩ → ⟨v, v⟩ = 1 for ⟨u, u′⟩ = bᵀb′ + ⟨L, L′⟩_F + 2⟨A, A′⟩_F, with the constrained matrix representation of `QuadPTFLearn.Residual`; reason: the normalization and inner product used in the proof (p.89)
--   - encoding: z ∈ V, w ∈ V⊥ independent standard Gaussian vectors; E_{z,w∼N(0,I)} → z = proj_V x, w = proj_{V⊥} x with x ∼ N(0, I_d); reason: the two projections of a standard Gaussian are independent standard Gaussians on V and V⊥
--   - encoding: i ∈ [k], k ∈ ℤ₊ → k a natural number, k = 0 not excluded; reason: at k = 0 F is constant, d_vF = 0 and the sum is empty, so both sides vanish; no instance of the source changes
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 9.4, p.89 (PDF p.91)

import Mathlib
import Definitions.Def_QuadPTFLearn_Residual

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 9.4, p.89 (PDF p.91).

Let `V ⊆ ℝᵈ`, `x = z + w` with `z ∈ V`, `w ∈ V⊥`. For `i ∈ [k]` let
`qᵢ(z, w) = aᵢ(z) + N_{uᵢ}(z, w)` with `uᵢ = (bᵢ, Lᵢ, Aᵢ)`, each `qᵢ` `(τ, V)`-regular with
`Var(qᵢ) ≤ 1`. Let `ψ : ℝᵏ → ℝ` be `C²` with bounded first and second derivatives,
`F = ψ(q₁, …, q_k)`, `D_j(ψ) = max ‖∂_{i₁} ⋯ ∂_{i_j} ψ‖_∞`. Then for every unit coefficient
direction `v = (b, L, A)` and every polynomial `p`,
`|E[p d_v F] − Σᵢ ⟨v, uᵢ⟩ E[p ∂ᵢψ(q₁, …, q_k)]| ≤ C τ (k D₁(ψ) + k² D₂(ψ)) ‖p‖₂`,
with `C > 0` universal.

**Formalization Note.** `qᵢ` is a polynomial of degree at most two (Definition 3.1 defines
regularity for those) whose difference with `N_{uᵢ}` depends only on `z`; `τ ∈ (0, 1)` as in
Definition 3.1. `D₁`, `D₂` are any bounds on the first and second partial derivatives (the
statement for every bound is the statement for the suprema). "Unit" is `⟨v, v⟩ = 1` with
`⟨u, u′⟩ = bᵀb′ + ⟨L, L′⟩_F + 2⟨A, A′⟩_F` (proof, p.89). -/
theorem lemma_9_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ) (V : Submodule ℝ (Pt d)) (τ : ℝ), 0 < τ → τ < 1 →
      ∀ (q : Fin k → Poly d) (u : Fin k → ResDir d),
        (∀ i, (q i).totalDegree ≤ 2 ∧ IsResDir V (u i) ∧
          (∀ x, peval (q i) x - resPoly V (u i) x =
            peval (q i) (projV V x) - resPoly V (u i) (projV V x)) ∧
          IsRegular τ V (q i) ∧ var (peval (q i)) ≤ 1) →
      ∀ ψ : (Fin k → ℝ) → ℝ, ContDiff ℝ 2 ψ → ∀ D₁ D₂ : ℝ,
        (∀ i y, |pd1 ψ i y| ≤ D₁) → (∀ i j y, |pd2 ψ i j y| ≤ D₂) →
      ∀ v : ResDir d, IsResDir V v → resInner v v = 1 → ∀ p : Poly d,
        |∫ x, peval p x * dRes V v (fun y => ψ (fun i => peval (q i) y)) x ∂gauss d -
            ∑ i, resInner v (u i) *
              ∫ x, peval p x * pd1 ψ i (fun j => peval (q j) x) ∂gauss d| ≤
          C * τ * ((k : ℝ) * D₁ + (k : ℝ) ^ 2 * D₂) * l2norm (peval p) := by sorry

end QuadPTFLearn
