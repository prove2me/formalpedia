-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_13
-- name    : RobustFracMP.claim_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:45.404127+00:00
-- url     : https://prove2.me/theorems/fdc65801-8b8f-4e9f-a8f3-8e33e04c4bb6
-- title:
--   Claim 3.13 — clustering cost against a possibly infeasible assignment
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite nonempty metric space and $z\ge1$. Let $y\in\mathbb R^P_{\ge0}$, $x\in\mathbb R^{P\times P}_{\ge0}$ and $\mu\in\mathbb R^P_{\ge0}$ satisfy:
--
--   1. $\sum_{q\in P:\ \mathrm{dist}^z(p,q)\le\mu_p}y_q\ge1$ for every $p\in P$;
--   2. $\sum_{q\in P}x_{p,q}=1$ for every $p\in P$;
--   3. $\mathrm{dist}^z(p,q)\le\mu_p$ for every pair $p,q$ with $x_{p,q}>0$.
--
--   Then
--
--   $$\mathrm{cost}_z(y)\le\sigma_z(x)+\sum_{p,q\in P}[x_{p,q}-y_q]_+\cdot\mu_p.$$
--
--   The claim converts an assignment that may violate (C2) into a bound on the clustering cost, paying $\mu_p$ per unit of excess; it is applied to $x^{(\beta)}$ in Lemma 3.16 and to an optimal assignment for $y^{(\beta^*)}$ in the proof of Lemma 3.1.
--
--   **Formalization Note** Condition 1 with $y\ge0$ gives $\sum_q y_q\ge1$, so $\mathrm{cost}_z(y)$ is the paper's value.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.13, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_RobustFracMP_assignCost
import Definitions.Def_RobustFracMP_fracCost

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.13 (cost of a fractional solution against a possibly infeasible assignment).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.13, pp.19–20 (PDF pp.21–22): "Suppose that a fractional solution y ∈ ℝ^P_{≥0}, a
fractional assignment x ∈ ℝ^{P×P}_{≥0}, and a vector µ ∈ ℝ^P_{≥0} satisfy the following conditions:
1. Each point p ∈ P satisfies Σ_{q∈P: dist^z(p,q)≤µ_p} y_q ≥ 1.
2. Each point p ∈ P satisfies Σ_{q∈P} x_{p,q} = 1.
3. Each pair p, q ∈ P with x_{p,q} > 0 satisfies dist^z(p, q) ≤ µ_p.
Then, it holds that cost_z(y) ≤ σ_z(x) + Σ_{p,q∈P} [x_{p,q} − y_q]_+ · µ_p."

**Formalization Note.** Condition 1 and `y ≥ 0` give `Σ y ≥ 1` (for nonempty `P`), so `cost_z(y)`
is the paper's (non-junk) value. `[a]_+` is `max a 0`. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_13 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (y : P → ℝ) (x : P → P → ℝ) (μ : P → ℝ)
    (hy : ∀ p, 0 ≤ y p) (hx : ∀ p q, 0 ≤ x p q) (hμ : ∀ p, 0 ≤ μ p)
    (h1 : ∀ p, 1 ≤ ∑ q ∈ Finset.univ.filter (fun q => dist p q ^ z ≤ μ p), y q)
    (h2 : ∀ p, ∑ q, x p q = 1)
    (h3 : ∀ p q, 0 < x p q → dist p q ^ z ≤ μ p) :
    fracCost z y ≤ assignCost z x + ∑ p, ∑ q, max (x p q - y q) 0 * μ p := by sorry

end RobustFracMP
