-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_scalar_entropy_estimates
-- name    : QAlgorithms.Papers.Independent.Information100.P54.scalar_entropy_estimates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:07:14.935211+00:00
-- url     : https://prove2.me/theorems/e756a487-7b67-408c-8c6c-1983e6b7b60e
-- title:
--   Lemma 1 (Scalar entropy estimates)
-- statement:
--   Let $0<\eta<1$, $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ with $g(0)=0$, and $c_\eta(x)=g(x)-g((1-\eta)x)$. For any probability law of a nonnegative integer-valued random variable $Z$ with finite mean $z$, its extended Shannon entropy in bits satisfies
--
--   $$H(Z)\le g(z).$$
--
--   Moreover, $c_\eta$ is strictly increasing and concave on $[0,\infty)$, and for every fixed finite $a\ge0$,
--
--   $$\lim_{r\to+\infty}\frac{g(ra)}r=0,$$
--
--   where $r$ is real. These estimates control photon-count entropy using only mean energy; entropy finiteness is a conclusion.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, PDF p. 9, Lemma 1 (Scalar entropy estimates)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped ENNReal Matrix

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF pp.8–9, Lemma 1: all three scalar estimates.
Finite mean does not assume finite entropy. The final limit is over real r. -/
theorem scalar_entropy_estimates (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    (∀ p : PMF ℕ, countMean p ≠ ⊤ →
      shannonEntropy p ≤ ENNReal.ofReal (thermalEntropy (countMean p).toReal)) ∧
    StrictMonoOn (lossRate eta) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (lossRate eta) ∧
    (∀ a : ℝ, 0 ≤ a →
      Tendsto (fun r : ℝ => thermalEntropy (r * a) / r) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P54

end
