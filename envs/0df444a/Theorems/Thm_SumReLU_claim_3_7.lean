-- Prove2me | Theorems.Thm_SumReLU_claim_3_7
-- name    : SumReLU.claim_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:34.278313+00:00
-- url     : https://prove2.me/theorems/55d1ff58-1390-45ae-8a61-922bbb4157a6
-- title:
--   Claim 3.7 — one projected step along a good direction shrinks the projective angle to $3r/5$
-- statement:
--   Let $0<\rho\le\pi/2$ and let $u,w\in S^{d-1}$ with $\theta_\pm(u,w)\le\rho$. Let $r$ be a unit vector with $r\cdot u=0$ and $|r\cdot\widehat{w^{\perp u}}|\ge0.9$. Let $\phi=4\rho/5$, $\eta=\tan\phi$, and
--   $$
--   u_+=\mathrm{proj}_{S^{d-1}}(u+\eta r),\qquad u_-=\mathrm{proj}_{S^{d-1}}(u-\eta r).
--   $$
--   Then
--   $$
--   \min_{z\in\{u,u_+,u_-\}}\theta_\pm(z,w)\le\frac{3\rho}{5}.
--   $$
--
--   This is the contraction step of the Refine procedure: given a direction correlated with the unknown part of $w$, one of the two candidate updates reduces the angular error by the factor $\chi=3/5$.
--
--   Differences from the source:
--   - encoding: the letter $r$ for both the radius and the unit direction → radius $\rho$, direction $r$; reason: the page uses one letter for two objects
--   - encoding: $\mathrm{proj}_{S^{d-1}}$ and $\widehat{w^{\perp u}}$ → `normalize` ($v\mapsto v/\|v\|_2$, $0\mapsto0$); reason: $u\pm\eta r\ne0$ since $u\perp r$; if $w^{\perp u}=0$ the hypothesis $|r\cdot0|\ge0.9$ fails, a case the page does not cover
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Claim 3.7, p.15 (PDF p.17); proof p.16 (PDF p.18)

import Mathlib
import Definitions.Def_SumReLU_thetaPM

namespace SumReLU

/-- **Claim 3.7** (One-step improvement in projective angle).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Claim 3.7, p.15 (PDF p.17); proof p.16 (PDF p.18): "Let 0 < r ≤ π/2. Let u, w ∈ S^{d−1} be such
that θ±(u, w) ≤ r. Let r ∈ u^⊥ be a unit vector such that |r · ŵ^{⊥u}| ≥ 0.9. Let ϕ := 4r/5,
η := tan ϕ, and define u₊ := proj_{S^{d−1}}(u + ηr), u₋ := proj_{S^{d−1}}(u − ηr). Then
min_{z∈{u,u₊,u₋}} θ±(z, w) ≤ 3r/5 = χr."

**Formalization Note.** The page uses the letter `r` both for the radius and for the bold unit
direction; here the radius is `ρ` and the direction is `r`. `proj_{S^{d−1}}` is `normalize`
(`u ± ηr ≠ 0` since `u ⊥ r` and `‖u‖ = 1`). -/
theorem claim_3_7 {d : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ Real.pi / 2)
    (u w : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : thetaPM u w ≤ ρ)
    (r : EuclideanSpace ℝ (Fin d)) (hr : ‖r‖ = 1) (hru : inner ℝ u r = 0)
    (hrw : (0.9 : ℝ) ≤ |inner ℝ r (normalize (perp u w))|) :
    min (thetaPM u w)
        (min (thetaPM (normalize (u + Real.tan (4 * ρ / 5) • r)) w)
          (thetaPM (normalize (u - Real.tan (4 * ρ / 5) • r)) w)) ≤ 3 * ρ / 5 := by sorry

end SumReLU
