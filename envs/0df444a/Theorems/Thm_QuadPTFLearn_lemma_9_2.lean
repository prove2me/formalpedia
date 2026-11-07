-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_9_2
-- name    : QuadPTFLearn.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:29.512195+00:00
-- url     : https://prove2.me/theorems/bd6ba53d-1f0a-41f4-8a59-36528de413c0
-- title:
--   Lemma 9.2, p.82 — a certificate $p=P(q_1,\dots,q_k)$ of degree $\le2k$ with $\mathbb E[fM_vp]\ge\Omega((\alpha/k)^{3k})$ when the $q_i$ are linear on $V^\perp$
-- statement:
--   Let $V\subseteq\mathbb R^d$, $x=z+w$ with $z\in V$, $w\in V^\perp$, and $f(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$, where $q_i(x)=a_i(z)+u_i\cdot w$ with $\|q_i\|=1$ and $a_i$ a polynomial of degree at most two depending only on $z$. Let $v\in V^\perp$ be a unit vector and $\alpha\in(0,1)$. If $\mathrm{Rand}_f(v)\ge\alpha$, there is a polynomial $p:\mathbb R^d\to\mathbb R$ with $\deg p\le2k$ and $\|p\|\le1$ such that
--   $$\mathbb E_{x\sim N(0,I)}[f(x)\,M_vp(x)]\ \ge\ c\,(\alpha/k)^{3k}$$
--   for a universal $c>0$. In particular, $p(x)=P(q_1(x),\dots,q_k(x))$ for a polynomial $P:\mathbb R^k\to\mathbb R$.
--
--   In the idealized Gaussian model the defining polynomials are linear in the residual coordinates, and the lemma gives a moment certificate for every high-influence direction there.
--
--   Differences from the source:
--   - reading: Ω((α/k)^{3k}) → c (α/k)^{3k} with a universal c > 0 chosen before d, k, V, f, v, α; reason: the non-weaker reading
--   - encoding: q_i(x) = a_i(z) + u_i · w with ∥q_i∥ = 1 → x ↦ a_i(x) + ⟪u_i, proj_{V⊥}x⟫ with a_i of degree ≤ 2 and a_i(x) = a_i(proj_V x), u_i ∈ ℝᵈ, Gaussian L² norm 1; reason: only the V⊥ part of u_i enters u_i · w
--   - encoding: the same p … In particular, p = P(q₁, …, q_k) → one ∃ p with both properties; reason: the "in particular" clause is about the same p
--   - encoding: i ∈ [k] → 1 ≤ k; reason: [k] for k ∈ ℤ₊
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 9.2, p.82 (PDF p.84)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 9.2, p.82 (PDF p.84).

Let `V ⊆ ℝᵈ`, `x = z + w`, `z ∈ V`, `w ∈ V⊥`, and `f(x) = 1{q₁(x) ≥ 0, …, q_k(x) ≥ 0}` with
`qᵢ(x) = aᵢ(z) + uᵢ · w`, `‖qᵢ‖ = 1`, `aᵢ` a polynomial of degree at most two depending only on
`z`. Let `v ∈ V⊥` be a unit vector and `α ∈ (0, 1)`. If `Rand_f(v) ≥ α`, there is a polynomial
`p` with `deg p ≤ 2k`, `‖p‖ ≤ 1` and `E_{x∼N(0,I)}[f(x) M_v p(x)] ≥ c (α/k)^{3k}`, and moreover
`p(x) = P(q₁(x), …, q_k(x))` for a polynomial `P : ℝᵏ → ℝ`.

**Formalization Note.** `Ω((α/k)^{3k})` is `c (α/k)^{3k}` with a universal `c > 0` chosen
before everything; the "in particular" clause is asserted for the same `p`. -/
theorem lemma_9_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d k : ℕ), 1 ≤ k → ∀ (V : Submodule ℝ (Pt d)) (a : Fin k → Poly d) (u : Fin k → Pt d),
        (∀ i, (a i).totalDegree ≤ 2 ∧ DependsOnlyOn V (a i)) →
        (∀ i, l2norm (fun x => peval (a i) x + ⟪u i, projV Vᗮ x⟫) = 1) →
      ∀ v ∈ Vᗮ, ‖v‖ = 1 → ∀ α : ℝ, 0 < α → α < 1 →
        α ≤ Rand (fun x => if ∀ i, 0 ≤ peval (a i) x + ⟪u i, projV Vᗮ x⟫ then (1 : ℝ) else 0) v →
        ∃ p : Poly d, p.totalDegree ≤ 2 * k ∧ l2norm (peval p) ≤ 1 ∧
          c * (α / k) ^ (3 * k) ≤
            ∫ x, (if ∀ i, 0 ≤ peval (a i) x + ⟪u i, projV Vᗮ x⟫ then (1 : ℝ) else 0) *
              peval (boundaryOp v p) x ∂gauss d ∧
          ∃ Q : MvPolynomial (Fin k) ℝ, ∀ x,
            peval p x = MvPolynomial.eval (fun i => peval (a i) x + ⟪u i, projV Vᗮ x⟫) Q := by sorry

end QuadPTFLearn
