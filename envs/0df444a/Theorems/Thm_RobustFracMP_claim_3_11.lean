-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_11
-- name    : RobustFracMP.claim_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:43.027437+00:00
-- url     : https://prove2.me/theorems/7bb1d9fc-3348-4706-bf10-48ff97b14d39
-- title:
--   Claim 3.11 — induction step of the local-density bound
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\alpha\in(0,1)$ and $\gamma\ge1$. Suppose that
--
--   $$\sum_{q\in B^{(\beta)}_p(\gamma r^{(\beta)}_p)}r^{(\beta)}_q\ge\alpha\lambda\qquad\text{for all }\beta>0\text{ and }p\in P.\qquad(13)$$
--
--   Then
--
--   $$\sum_{q\in B^{(\beta)}_p(2^{2z}\gamma\, r^{(\beta)}_p)}r^{(\beta)}_q\ge\min\{2\alpha,1\}\cdot\lambda\qquad\text{for all }\beta>0\text{ and }p\in P.\qquad(14)$$
--
--   Applying the claim $z$ times to Claim 3.10 doubles the density factor each time until it reaches $1$, which proves Lemma 3.9.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.11, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.11 (induction step for Lemma 3.9).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.11, p.18 (PDF p.20): "Given parameters α ∈ (0, 1) and γ ≥ 1, if it holds that
Σ_{q∈B^{(β)}_p(γ·r^{(β)}_p)} r^{(β)}_q ≥ α · λ, ∀β > 0, ∀p ∈ P, (13) then it also holds that
Σ_{q∈B^{(β)}_p(2^{2z}·γ·r^{(β)}_p)} r^{(β)}_q ≥ min{2α, 1} · λ, ∀β > 0, ∀p ∈ P. (14)"

The printed quantifier structure is kept: (13) for all `β > 0` and all `p` implies (14) for all
`β > 0` and all `p`, for the fixed space `(P, dist)`, `z` and `λ`.

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_11 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (α γ : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hγ : 1 ≤ γ)
    (h13 : ∀ β : ℝ, 0 < β → ∀ p : P,
      α * lam ≤ ∑ q ∈ ball z β p (γ * mpRadius z dist β lam p), mpRadius z dist β lam q) :
    ∀ β : ℝ, 0 < β → ∀ p : P,
      min (2 * α) 1 * lam ≤
        ∑ q ∈ ball z β p (2 ^ (2 * z) * γ * mpRadius z dist β lam p), mpRadius z dist β lam q := by sorry

end RobustFracMP
