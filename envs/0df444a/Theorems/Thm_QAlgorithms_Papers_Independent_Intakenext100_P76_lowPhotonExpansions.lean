-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_lowPhotonExpansions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.lowPhotonExpansions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:53:29.078805+00:00
-- url     : https://prove2.me/theorems/a37bf531-3f98-4061-9cdd-57f3bfe0c66d
-- title:
--   Low-photon nats expansions and diverging photon efficiency
-- statement:
--   Let $G(x)=(\ln2)g(x)$ and $B(x)=(\ln2)h_2((1-e^{-2x})/2)$ denote the two Holevo expressions in nats per mode. As $x\downarrow0$ through strictly positive photon numbers,
--
--   $$
--   G(x)=-x\ln x+x+\frac{x^2}{2}+O(x^3),\qquad
--   B(x)=-x\ln x+x+x^2\ln x+O(x^2).
--   $$
--
--   Explicitly, there are positive constants $C,D,\delta$, with $\delta\le1$, bounding the absolute remainders by $Cx^3$ and $Dx^2$ for every $0<x<\delta$. Furthermore,
--
--   $$
--   \frac{G(x)}x+\ln x\longrightarrow1,\qquad
--   \frac{B(x)}x+\ln x\longrightarrow1,\qquad
--   \frac{G(x)}x,\ \frac{B(x)}x\longrightarrow+\infty.
--   $$
--
--   These limits express the common first two terms and the unbounded photon efficiencies.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 13, §6.2, (6.15)–(6.16) and adjacent efficiency assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.13, (6.15)–(6.16) and the adjacent photon-efficiency assertion.
Nats are explicit. Remainders are O(x^3) and O(x^2), respectively, as x goes
to zero from the right. In particular no evaluation at x=0 or negative x is used. -/
theorem lowPhotonExpansions :
    (∃ C D delta : ℝ, 0 < C ∧ 0 < D ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x < delta →
        |thermalEntropyNats x - (-x * Real.log x + x + x ^ 2 / 2)| ≤ C * x ^ 3 ∧
        |bpskHolevoNats x - (-x * Real.log x + x + x ^ 2 * Real.log x)| ≤ D * x ^ 2) ∧
    Tendsto (fun x : ℝ => thermalEntropyNats x / x + Real.log x) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun x : ℝ => bpskHolevoNats x / x + Real.log x) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun x : ℝ => thermalEntropyNats x / x) (𝓝[>] 0) atTop ∧
    Tendsto (fun x : ℝ => bpskHolevoNats x / x) (𝓝[>] 0) atTop := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
