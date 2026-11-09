-- Prove2me | Theorems.Thm_RobustFracMP_fact_2_1
-- name    : RobustFracMP.fact_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:56:51.579571+00:00
-- url     : https://prove2.me/theorems/30b76c00-aeb6-4206-a034-6e74a81b4663
-- title:
--   Fact 2.1 — generalized triangle inequality for power-$z$ distances
-- statement:
--   Let $(P,\mathrm{dist})$ be a metric space and $z\ge1$ an integer. For all $p,q,t\in P$,
--
--   $$\mathrm{dist}^z(p,q)\le 2^{z-1}\bigl(\mathrm{dist}^z(p,t)+\mathrm{dist}^z(t,q)\bigr).$$
--
--   This replaces the triangle inequality for power-$z$ distances, which are not metrics for $z\ge2$; it is used in every smoothness and density bound of Section 3.1.
--
--   Differences from the source: none.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Fact 2.1, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **Fact 2.1 (Generalized Triangle Inequality).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Fact 2.1, p.10 (PDF p.12): "Let (P, dist) be a metric space. For any p, q, t ∈ P, it holds that
dist^z(p, q) ≤ 2^{z−1} · (dist^z(p, t) + dist^z(t, q))."

**Formalization Note.** `z : ℕ` with `1 ≤ z` (the standing assumption of p.10), so `z − 1` is the
true difference. The metric space need not be finite. -/
theorem fact_2_1 {P : Type*} [MetricSpace P] (z : ℕ) (hz : 1 ≤ z) (p q t : P) :
    dist p q ^ z ≤ 2 ^ (z - 1) * (dist p t ^ z + dist t q ^ z) := by sorry

end RobustFracMP
