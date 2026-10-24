-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark7
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:40:14.23087+00:00
-- url     : https://prove2.me/theorems/08186e86-3e43-4ba9-b3a4-6e02236af531
-- title:
--   remark7
-- statement:
--   For every fixed real entropy difference $\Delta$, sufficiently large finite dimensions admit the explicit states $\sigma_d=\tau_d((1+t_d)/2)$ and $\rho_d=\tau_d((1-t_d)/2)$ with $t_d=\Delta/\log(d-1)$. There are a positive constant $C$ and an integer threshold $d_0\ge3$, chosen before $d$, such that for all $d\ge d_0$ these are normalized states and
--
--   $$S(\sigma_d)-S(\rho_d)=\Delta,\qquad D(\sigma_d\|\rho_d)\le C\frac{2\Delta^2}{\log^2(d-1)}.$$
--
--   Thus $M(\Delta,d)\to0$. Any real lower bound valid across all finite dimensions at this fixed difference is at most zero, and zero relative entropy is unattainable at a nonzero difference. Moreover, for $d'>d\ge2$ and $|\Delta|\le\log d$,
--
--   $$M(\Delta,d')\le M(\Delta,d),$$
--
--   strictly if $\Delta\ne0$. The cited infinite-dimensional Klein identity is background; this paper supplies finite-rank witnesses precluding a positive dimension-independent bound.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 6, remark7

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 7, PDF pp.6--7: explicit witnesses, dimension limit and strict dimension monotonicity.
The infinite-Hilbert-space Klein identity cited there is background, not a new assertion here. -/
theorem remark7 :
    (∀ delta : ℝ, ∃ c > 0, ∃ d0 : ℕ, 3 ≤ d0 ∧ ∀ d ≥ d0,
      let t := delta / Real.log ((d : ℝ) - 1)
      ∃ ha : IsDensityMatrix (family d ((1 + t) / 2)),
      ∃ hb : IsDensityMatrix (family d ((1 - t) / 2)),
        difference (family d ((1 + t) / 2)) (family d ((1 - t) / 2)) = delta ∧
        stateRelativeNats ⟨family d ((1 + t) / 2), ha⟩ ⟨family d ((1 - t) / 2), hb⟩ ≤
          (c * (2 * delta ^ 2 / (Real.log ((d : ℝ) - 1)) ^ 2) : ℝ)) ∧
    (∀ delta : ℝ, Tendsto (fun d : ℕ => tightBound d delta) atTop (nhds 0)) ∧
    (∀ d : ℕ, 2 ≤ d → ∀ a b : EntropyState d, difference a.val b.val ≠ 0 → 0 < stateRelativeNats a b) ∧
    (∀ delta b : ℝ, (∀ d : ℕ, 2 ≤ d → ∀ a r : EntropyState d,
      difference a.val r.val = delta → (b : EReal) ≤ stateRelativeNats a r) → b ≤ 0) ∧
    (∀ d d' : ℕ, 2 ≤ d → d < d' → ∀ delta ∈ Set.Icc (-Real.log d) (Real.log d),
      tightBound d' delta ≤ tightBound d delta ∧
      (delta ≠ 0 → tightBound d' delta < tightBound d delta)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
