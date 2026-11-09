-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_theorem_3_4
-- name    : SpatialHalfspace.FullLabels.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:34.517204+00:00
-- url     : https://prove2.me/theorems/195c7249-c3df-49fc-ad33-db361d4816e1
-- title:
--   Theorem 3.4 — Risk–distortion reduction
-- statement:
--   Let $D\ge 2$ and $q=\lfloor D/2\rfloor$. For every $\sigma\in\{0,1\}^U$,
--
--   $$R^*_{\bar P^\sigma}(H_D)=2\alpha+\frac{\alpha}{q}\,\big|\{e: Z_e(\sigma)=0\}\big|\ \le\ 3\alpha=\frac{3}{64}.\tag{20}$$
--
--   Let $d_H$ be the Hamming distance on $\{0,1\}^q$. Every $h\in H_D$ satisfies
--
--   $$R_{\bar P^\sigma}(h)-R^*_{\bar P^\sigma}(H_D)\ \ge\ \frac{\alpha}{q}\,d_H\big((h(a_e))_{e},\,Z(\sigma)\big).\tag{21}$$
--
--   Thus a proper learner with small excess risk must recover most of the equality bits $Z_e(\sigma)$ from its midpoint predictions.
--
--   Differences from the source:
--
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 9, PDF p. 10, Theorem 3.4, eqs. (20)–(21), PDF p. 10

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Theorem 3.4 (Risk–distortion reduction), printed p. 9. For every `σ ∈ {0,1}^U`,
(20) `R*_{P̄^σ}(H_D) = 2α + (α/q)|{e : Z_e(σ) = 0}| ≤ 3α = 3/64`, and (21) every `h ∈ H_D`
satisfies `R_{P̄^σ}(h) − R*_{P̄^σ}(H_D) ≥ (α/q) d_H((h(a_e))_e, Z(σ))`. -/
theorem theorem_3_4 (D : ℕ) (hD : 2 ≤ D) (σ : Term D → Bool) :
    optRisk (mixture (PM D σ)) =
        2 * alpha + alpha / ((D / 2 : ℕ) : ℝ) *
          ((Finset.univ.filter fun e : Fin (D / 2) => Zvec σ e = false).card : ℝ) ∧
      2 * alpha + alpha / ((D / 2 : ℕ) : ℝ) *
          ((Finset.univ.filter fun e : Fin (D / 2) => Zvec σ e = false).card : ℝ) ≤ 3 * alpha ∧
      3 * alpha = 3 / 64 ∧
      ∀ h ∈ homHalfspaces D,
        alpha / ((D / 2 : ℕ) : ℝ) * (hammingDist (fun e => h (mid e)) (Zvec σ) : ℝ) ≤
          risk (mixture (PM D σ)) h - optRisk (mixture (PM D σ)) := by sorry

end SpatialHalfspace.FullLabels
