-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_7
-- name    : RobustFracMP.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:07.170208+00:00
-- url     : https://prove2.me/theorems/7d601baf-9d35-4ffa-8f01-eb08981ccb54
-- title:
--   Lemma 3.7 — smoothness of $r^{(\beta)}$ in the location
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   For every scale factor $\beta>0$ and all $p,q\in P$,
--
--   $$r^{(\beta)}_p\le r^{(2^{z-1}\beta)}_q+2^{z-1}\beta\,\mathrm{dist}^z(p,q)\le2^{z-1}\bigl(r^{(\beta)}_q+\beta\,\mathrm{dist}^z(p,q)\bigr).$$
--
--   Both inequalities of the chain are asserted. Nearby points have comparable radii; this is the smoothness property that replaces the $z=1$ argument of [BCG+24] in the dual-feasibility step of Lemma 3.14, and it gives the inclusion of close pairs in small balls in Claims 3.18 and 3.21.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.7, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.7 (smoothness of r^{(β)} in the location).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.7, p.15 (PDF p.17): "For any scale factor β > 0 and any two points p, q ∈ P,
r^{(β)}_p ≤ r^{(2^{z−1}β)}_q + 2^{z−1} · β · dist^z(p, q) ≤ 2^{z−1} · (r^{(β)}_q + β · dist^z(p, q))."

Both inequalities of the chain are stated.

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_7 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β) (p q : P) :
    mpRadius z dist β lam p ≤
        mpRadius z dist (2 ^ (z - 1) * β) lam q + 2 ^ (z - 1) * β * dist p q ^ z ∧
      mpRadius z dist (2 ^ (z - 1) * β) lam q + 2 ^ (z - 1) * β * dist p q ^ z ≤
        2 ^ (z - 1) * (mpRadius z dist β lam q + β * dist p q ^ z) := by sorry

end RobustFracMP
