-- Prove2me | Theorems.Thm_RobustFracMP_algorithm_1_well_defined
-- name    : RobustFracMP.algorithm_1_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:58.851634+00:00
-- url     : https://prove2.me/theorems/d6d490c1-808e-4db6-9e19-07684b0b90ea
-- title:
--   Algorithm 1 is well defined — eq. (8) has a unique root in $(0,\lambda]$, and (12)
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   1. For every distance function $D:P\times P\to\mathbb R$ with $D\ge0$ and $D(p,p)=0$ for all $p$, every $\beta>0$ and every $p\in P$, the value $r=r^{(\beta)}_p$ computed for $D$ satisfies $0<r\le\lambda$,
--   $$\sum_{q\in P}\bigl[r-\beta D(p,q)^z\bigr]_+=\lambda,$$
--   and it is the only $r>0$ satisfying this equation.
--   2. On the true metric, (8) holds in the equivalent form
--   $$\sum_{q\in B^{(\beta)}_p(r^{(\beta)}_p)}\bigl(r^{(\beta)}_p-\beta\,\mathrm{dist}^z(p,q)\bigr)=\lambda.\qquad(12)$$
--
--   This is the well-posedness of Algorithm 1: it pins the radius as the root of (8), so that every statement about $r^{(\beta)}$ and $y^{(\beta)}$, including the goal, is about the algorithm's actual output. Part 1 covers the distorted distance of Lemma 3.1, since (9) forces $\widetilde{\mathrm{dist}}\ge0$ and $\widetilde{\mathrm{dist}}(p,p)=0$.
--
--   Differences from the source:
--   - generalization: eq. (8) for the input distance of MP_β (dist, or the distorted distance of Lemma 3.1), β ∈ (0, 1) → every D : P → P → ℝ with D ≥ 0 and D(p, p) = 0, every β > 0; reason: both distances of the paper satisfy these conditions, and Section 3.1 uses r^{(β)} for every β > 0 (p.14); the statement specializes to each
--   - encoding: 'compute a value r^{(β)}_p > 0 such that (8)' → r^{(β)}_p := sSup {r ≥ 0 | Σ_q [r − βD(p,q)^z]_+ ≤ λ}; reason: the statement proves this is the unique positive root of (8), so it is the value the algorithm computes
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Algorithm 1, eq. (8), p.12 (PDF p.14); §1.1.1, p.5 (PDF p.7); eq. (12), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball

set_option autoImplicit false

namespace RobustFracMP

/-- **Algorithm 1 is well defined: eq. (8) has a unique positive root, it lies in (0, λ], and
`mpRadius` is that root; the equivalent form (12).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Algorithm 1, line 1, eq. (8), p.12 (PDF p.14): "compute a value r^{(β)}_p > 0 such that
Σ_{q∈P} [r^{(β)}_p − β · dist^z(p, q)]_+ = λ"; §1.1.1, p.5 (PDF p.7): "a value 0 < r^{(β)}_p ≤ λ";
eq. (12), p.15 (PDF p.17): "the defining equation for r^{(β)}_p in (8) is equivalent to
Σ_{q∈B^{(β)}_p(r^{(β)}_p)} (r^{(β)}_p − β · dist^z(p, q)) = λ."

Part 1 is stated for every distance function `D : P → P → ℝ` with `D ≥ 0` and `D(p, p) = 0`, which
covers both `dist` and the distorted `\tilde{dist}` of Lemma 3.1 (by (9), `dist ≤ \tilde{dist} ≤
ε^{−2} dist` forces both properties). Part 2 is (12) on the true metric.

**Formalization Note.** `[a]_+` is `max a 0`. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem algorithm_1_well_defined {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    (∀ D : P → P → ℝ, (∀ p q, 0 ≤ D p q) → (∀ p, D p p = 0) → ∀ p : P,
      0 < mpRadius z D β lam p ∧ mpRadius z D β lam p ≤ lam ∧
      ∑ q, max (mpRadius z D β lam p - β * D p q ^ z) 0 = lam ∧
      ∀ r : ℝ, 0 < r → ∑ q, max (r - β * D p q ^ z) 0 = lam → r = mpRadius z D β lam p) ∧
    ∀ p : P, ∑ q ∈ ball z β p (mpRadius z dist β lam p),
      (mpRadius z dist β lam p - β * dist p q ^ z) = lam := by sorry

end RobustFracMP
