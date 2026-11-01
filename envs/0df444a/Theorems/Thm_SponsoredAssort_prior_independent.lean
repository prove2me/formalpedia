-- Prove2me | Theorems.Thm_SponsoredAssort_prior_independent
-- name    : SponsoredAssort.prior_independent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:55:34.811926+00:00
-- url     : https://prove2.me/theorems/2eae2fdb-ca7c-4c2c-ba9d-3d107d884154
-- title:
--   (Prior independent), OA p.4 — the worst-case prior is a point mass
-- statement:
--   Let $r>0$. For every deterministic mechanism $m$ the worst case over priors equals the worst case over single profiles,
--
--   $$
--   \inf_{F\in\mathcal P(\mathbb R^n_+)}\frac{\mathbb E_{v\sim F}[R(m,v)]}{\mathbb E_{v\sim F}[R(m^{FB},v)]}=\inf_{v\in\mathbb R^n_+}\frac{R(m,v)}{R(m^{FB},v)},
--   $$
--
--   and consequently
--
--   $$
--   \gamma^{PI}(r)=\sup_{m\in M}\ \inf_{v\in\mathbb R^n_+}\frac{R(m,v)}{R(m^{FB},v)} .
--   $$
--
--   The prior-independent problem is thus a prior-free one, which reduces the upper bound of Proposition 5.4 to exhibiting a bad profile for each IC mechanism.
--
--   Differences from the source:
--   - encoding: infimum over $v\in\mathbb R^n_+$ → over $v\ne0$; reason: $R(m^{FB},0)=0$, so the ratio is $0/0$ at $v=0$, as at the prior $\delta_0$
--   - generalization: the identity for $\gamma^{PI}(r)$ → also the identity for each mechanism $m$, IC or not; reason: the per-mechanism identity implies the printed one
--   - encoding: expectations over $\mathcal P(\mathbb R^n_+)$ → lower Lebesgue integrals, prior $\delta_0$ excluded; reason: same as Definition 2.2's encoding
--   - generalization: standing order $r_1\ge\dots\ge r_n$ → any $r>0$; reason: not used; specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix A.2, (Prior independent), OA p.4

import Mathlib
import Definitions.Def_SponsoredAssort_gammaPI

open scoped NNReal ENNReal

namespace SponsoredAssort

/-- **(Prior independent)** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Appendix A.2,
OA p.4). For revenues `r > 0`,
`γ^PI(r) = sup_{m ∈ M} inf_{v ∈ ℝⁿ₊} R(m, v) / R(m^FB, v)`; more precisely, for every
deterministic mechanism `m` the worst case over priors equals the worst case over points,
`inf_F E_F[R(m, v)] / E_F[R(m^FB, v)] = inf_v R(m, v) / R(m^FB, v)`.

**Formalization Note.** The pointwise infimum excludes `v = 0`, where `R(m^FB, 0) = 0` and the
ratio is `0/0`, exactly as `worstCaseRatio` excludes the point mass at `0`. Ratios are in
`ℝ≥0∞`. The first clause holds for every mechanism, IC or not; the second is the printed
display. -/
theorem prior_independent {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (∀ m : Mechanism n, worstCaseRatio r m =
      ⨅ (v : Attr n) (_ : v ≠ 0),
        ENNReal.ofReal (welfare r (m.alloc v) v) / ENNReal.ofReal (firstBest r v)) ∧
    gammaPI r = ⨆ (m : Mechanism n) (_ : IsIC r m) (_ : IsIR r m),
      ⨅ (v : Attr n) (_ : v ≠ 0),
        ENNReal.ofReal (welfare r (m.alloc v) v) / ENNReal.ofReal (firstBest r v) := by sorry

end SponsoredAssort
