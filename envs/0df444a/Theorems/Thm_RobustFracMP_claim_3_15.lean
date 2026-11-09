-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_15
-- name    : RobustFracMP.claim_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:57.319899+00:00
-- url     : https://prove2.me/theorems/2d8d81e2-55d6-4300-9c94-b35d1f75956e
-- title:
--   Claim 3.15 — [BCG+24, Lemma 13.6] for power-$z$ distances
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\beta^*=2^{-z-1}$ and $0<\beta\le\beta^*$. For every $p\in P$,
--
--   $$r^{(\beta)}_p+\sum_{q\in P}\frac1\lambda\bigl[r^{(\beta)}_p-\beta\,\mathrm{dist}^z(p,q)\bigr]_+\cdot\beta\,\mathrm{dist}^z(p,q)\le r^{(2\beta)}_p.$$
--
--   Doubling the scale factor raises each radius by at least the $\beta$-scaled assignment cost of its point; summed over $p$ this is the step from $\sigma_z(x^{(\beta)})$ to $\beta^{-1}(\|r^{(2\beta)}\|_1-\lambda\|y^{(\beta)}\|_1)$ in Lemma 3.14.
--
--   Differences from the source:
--   - reading: stated inside the proof of Lemma 3.12, whose statement fixes β ∈ (0, β*], β* = 2^{−z−1} (p.19) → hypotheses 0 < β and β ≤ 1 / 2 ^ (z + 1); reason: the claim's own sentence names no range for β; its context does
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.15, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.15 ([BCG+24, Lemma 13.6]).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Claim 3.15, p.21 (PDF p.23): "For each point p ∈ P,
r^{(β)}_p + Σ_{q∈P} (1/λ) · [r^{(β)}_p − β · dist^z(p, q)]_+ · β · dist^z(p, q) ≤ r^{(2β)}_p."

The claim sits inside the proof of Lemma 3.12, whose statement fixes the scale factor
`β ∈ (0, β*]` with `β* := 2^{−z−1}` (p.19); that range is a hypothesis here.

**Formalization Note.** Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_15 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β)
    (hβs : β ≤ 1 / 2 ^ (z + 1)) (p : P) :
    mpRadius z dist β lam p +
        ∑ q, 1 / lam * max (mpRadius z dist β lam p - β * dist p q ^ z) 0 * (β * dist p q ^ z) ≤
      mpRadius z dist (2 * β) lam p := by sorry

end RobustFracMP
