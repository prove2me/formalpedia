-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_5
-- name    : RobustFracMP.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:59.002434+00:00
-- url     : https://prove2.me/theorems/de32c3f5-b1ce-40aa-af96-dcaf79cc23ac
-- title:
--   Lemma 3.5 — size bound for small balls
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   For every scale factor $\beta>0$, point $p\in P$ and radius $0<r<r^{(\beta)}_p$,
--
--   $$\bigl|B^{(\beta)}_p(r)\bigr|\le\frac{\lambda}{r^{(\beta)}_p-r}.$$
--
--   The bound is used with $r=r^{(\beta^*)}_q/2$ in Claim 3.21, where it gives $|B^{(\beta^*)}_q(r^{(\beta^*)}_q/2)|\le2\lambda/r^{(\beta^*)}_q$.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.5, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.5 (size bound for small balls).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.5, p.15 (PDF p.17): "|B^{(β)}_p(r)| ≤ λ / (r^{(β)}_p − r), for any scale factor β > 0,
point p ∈ P and radius 0 < r < r^{(β)}_p."

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_5 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β) (p : P) (r : ℝ)
    (hr : 0 < r) (hrr : r < mpRadius z dist β lam p) :
    ((ball z β p r).card : ℝ) ≤ lam / (mpRadius z dist β lam p - r) := by sorry

end RobustFracMP
