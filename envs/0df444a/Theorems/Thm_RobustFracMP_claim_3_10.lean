-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_10
-- name    : RobustFracMP.claim_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:41.602552+00:00
-- url     : https://prove2.me/theorems/bf35ede0-3c2e-44e7-8dd9-50a2e60f65ef
-- title:
--   Claim 3.10 — base case of the local-density bound
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   For every scale factor $\beta>0$ and every $p\in P$,
--
--   $$\sum_{q\in B^{(\beta)}_p(2^z r^{(\beta)}_p)}r^{(\beta)}_q\ge\frac1{2^z}\,\lambda.$$
--
--   It is the base case of the induction proving Lemma 3.9.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.10, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.10 (base case for Lemma 3.9).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.10, p.17 (PDF p.19): "For any scale factor β > 0 and every point p ∈ P,
Σ_{q∈B^{(β)}_p(2^z·r^{(β)}_p)} r^{(β)}_q ≥ (1/2^z) · λ."

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_10 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β) (p : P) :
    1 / 2 ^ z * lam ≤
      ∑ q ∈ ball z β p (2 ^ z * mpRadius z dist β lam p), mpRadius z dist β lam q := by sorry

end RobustFracMP
