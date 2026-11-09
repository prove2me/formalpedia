-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_9
-- name    : RobustFracMP.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:48.562196+00:00
-- url     : https://prove2.me/theorems/87ba0de4-839c-4a9f-8bb3-31d7df006338
-- title:
--   Lemma 3.9 — local density of the radii, $\gamma^*=2^{2z^2+z}$
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\gamma^*=2^{2z^2+z}$. For every scale factor $\beta>0$ and every $p\in P$,
--
--   $$\sum_{q\in B^{(\beta)}_p(\gamma^*\, r^{(\beta)}_p)}r^{(\beta)}_q\ge\lambda.$$
--
--   Every point sees at least one unit of opening $y^{(\beta)}=r^{(\beta)}/\lambda$ within scaled power distance $\gamma^*r^{(\beta)}_p$. It gives premise 1 of Claim 3.13 in Lemma 3.16 and in the proof of Lemma 3.1, and in particular $\|y^{(\beta)}\|_1\ge1$.
--
--   **Formalization Note** The explicit constant $\gamma^*=2^{2z^2+z}$ is used, not $2^{O(z^2)}$.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.9, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.9 (local density of r^{(β)}).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.9, p.17 (PDF p.19): "Let γ* := 2^{2z²+z} = 2^{O(z²)}. For any scale factor β > 0 and
every point p ∈ P, Σ_{q∈B^{(β)}_p(γ*·r^{(β)}_p)} r^{(β)}_q ≥ λ."

**Formalization Note.** The explicit constant `γ* = 2^{2z²+z}` is used, not `2^{O(z²)}`. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_9 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β) (p : P) :
    lam ≤ ∑ q ∈ ball z β p (2 ^ (2 * z ^ 2 + z) * mpRadius z dist β lam p),
      mpRadius z dist β lam q := by sorry

end RobustFracMP
