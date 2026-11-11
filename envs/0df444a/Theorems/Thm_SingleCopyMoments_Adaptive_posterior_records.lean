-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_posterior_records
-- name    : SingleCopyMoments.Adaptive.posterior_records
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:09.722108+00:00
-- url     : https://prove2.me/theorems/f4e5f96b-1479-42f3-a043-d9015b48f6f0
-- title:
--   Lemma 33 — Posterior mean and exceptional records
-- statement:
--   Fix $r\ge2$, $0<\alpha\le1/100$, $\kappa\ge1$, and $\alpha\le1/(8\kappa)$. At every frozen rank-one history $H_n$ with $\|S_n\|_{op}<\kappa$, the physical posterior is normalized and integrable and obeys
--
--   $$\frac{I}{2d}\preceq\mathbb E_\theta[\rho_\theta\mid H_n]\preceq\frac{2I}d.$$
--
--   For every budget $T\le d$ with $2T<\kappa d$, uniformly in $\theta$ and the adaptive rank-one representation,
--
--   $$P_\theta^{(T)}(G_\kappa^c)\le d\left(\frac{2eT}{\kappa d}\right)^\kappa.$$
--
--   The probability is for the original experiment running all rounds. The posterior is the cutoff-weighted Gaussian product likelihood with the projectors frozen; no posterior independence is assumed. Rank-one refinement is confined to the analysis, and the goal covers arbitrary POVMs.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: conditional posterior at every good history and arbitrary adaptive strategy → the explicit frozen-history posterior and any measurable rank-one density representation of the published protocol; reason: the effect-density equality retains continuous outcomes; refinement is not a premise of the goal
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 33, (7.18)–(7.19), printed p. 35 (PDF p. 37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 33, printed pp.35–36 (PDF pp.37–38). -/
theorem posterior_records (r : ℕ) (hr : 2 ≤ r) (α κ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1/100) (hκ : 1 ≤ κ) (hακ : α ≤ 1/(8*κ))
    (d : ℕ) (hd : 0 < d) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi/r)) :
    (∀ N : ℕ, ∀ H : FrozenHistory d N, Frozen H → opNorm (projectorSum H) < κ →
      IsProbabilityMeasure (posterior r α θ H) ∧
      Integrable (hardMatrix α θ) (posterior r α θ H) ∧
      Loewner ((1/(2*(d : ℝ))) • (1 : Op d))
        (∫ g, hardMatrix α θ g ∂posterior r α θ H) ∧
      Loewner (∫ g, hardMatrix α θ g ∂posterior r α θ H) ((2/(d : ℝ)) • (1 : Op d))) ∧
    (∀ T : ℕ, T ≤ d → 2*(T : ℝ) < κ*d → ∀ P : Protocol d, ∀ R : Refinement hd P,
      IsProbabilityMeasure (ensembleLaw hd P r α θ T) ∧
      (ensembleLaw hd P r α θ T) (goodRecords R T κ)ᶜ ≤
        ENNReal.ofReal ((d : ℝ) * (2*Real.exp 1*T/(κ*d))^κ)) := by sorry

end SingleCopyMoments.Adaptive
