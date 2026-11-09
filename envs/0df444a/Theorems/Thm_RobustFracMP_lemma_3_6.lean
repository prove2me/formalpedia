-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_6
-- name    : RobustFracMP.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:56.788908+00:00
-- url     : https://prove2.me/theorems/e1518c23-55ad-4317-bbae-f6bdd0396178
-- title:
--   Lemma 3.6 — smoothness of $r^{(\beta)}$ in the scale factor
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   For all scale factors $\beta\ge\beta'>0$ and every $p\in P$,
--
--   $$\frac{\beta'}{\beta}\,r^{(\beta)}_p\le r^{(\beta')}_p\le r^{(\beta)}_p.$$
--
--   Scaling $\beta$ by a factor $c\ge1$ changes the radii by a factor of at most $c$; this gives the second inequality of Lemma 3.7.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.6, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.6 (smoothness of r^{(β)} in β).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.6, p.15 (PDF p.17): "(β′/β) · r^{(β)} ≤ r^{(β′)} ≤ r^{(β)}, for any scale factors
β ≥ β′ > 0." Vector inequalities are entrywise (p.10).

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_6 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β β' : ℝ) (hβ' : 0 < β') (hle : β' ≤ β) :
    ∀ p : P, β' / β * mpRadius z dist β lam p ≤ mpRadius z dist β' lam p ∧
      mpRadius z dist β' lam p ≤ mpRadius z dist β lam p := by sorry

end RobustFracMP
