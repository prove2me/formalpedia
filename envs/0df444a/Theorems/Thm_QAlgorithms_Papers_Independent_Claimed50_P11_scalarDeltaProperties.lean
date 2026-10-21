-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P11_scalarDeltaProperties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P11.scalarDeltaProperties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:24:19.771888+00:00
-- url     : https://prove2.me/theorems/0cd65952-40c9-4abe-85fc-067a4d0f1cf9
-- title:
--   Thermal correction function and exact scalar deficit bound
-- statement:
--   Let $g(N)=(N+1)\ln(N+1)-N\ln N$ for $N\ge0$, with $0\ln0=0$, and set $f(x)=g^{-1}(\ln x)$. On $x\ge1$, define
--
--   $$
--   \delta(x)=f(x)-x/e+\tfrac12.
--   $$
--
--   The function $\delta$ is convex and nonincreasing, tends to zero as $x\to+\infty$, and satisfies $\delta(1)=\tfrac12-\tfrac1e$ and $0\le\delta(x)\le\delta(1)$. For $x_A,x_B\ge1$ and $0\le\lambda\le1$, put $m=\lambda x_A+(1-\lambda)x_B$. Then
--
--   $$
--   \delta(m)\ge\lambda\delta(x_A)+(1-\lambda)\delta(x_B)
--   -\left(\tfrac12-\tfrac1e\right),
--   $$
--
--   and the gap identity is
--
--   $$
--   f(m)-\lambda f(x_A)-(1-\lambda)f(x_B)
--   =\delta(m)-\lambda\delta(x_A)-(1-\lambda)\delta(x_B).
--   $$
--
--   The exact constant controls the scalar deficit without assuming the EPnI.
-- source:
--   A generalization of the Entropy Power Inequality to Bosonic Quantum Systems, arXiv:1402.0404v2, PDF p. 23, §VI.B Eqs. (105)–(109), with §II.C p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P11

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

/-- PDF pp.9,23,24 Eqs.(105)-(109): convexity, nonincrease, limit,
endpoint value, range, the exact uniform deficit bound, and the Jensen-gap
identity. The entire positive constant 1/2-1/e is subtracted in Eq.(108).
The source's word decreasing is read as nonincreasing on its stated domain. -/
theorem scalarDeltaProperties :
    ConvexOn ℝ (Set.Ici 1) entropyPowerDelta ∧
    AntitoneOn entropyPowerDelta (Set.Ici 1) ∧
    Tendsto entropyPowerDelta atTop (nhds 0) ∧
    entropyPowerDelta 1 = 1 / 2 - 1 / Real.exp 1 ∧
    (∀ x : ℝ, 1 ≤ x →
      0 ≤ entropyPowerDelta x ∧ entropyPowerDelta x ≤ entropyPowerDelta 1) ∧
    (∀ lambda xA xB : ℝ, 0 ≤ lambda → lambda ≤ 1 → 1 ≤ xA → 1 ≤ xB →
      lambda * entropyPowerDelta xA + (1 - lambda) * entropyPowerDelta xB -
          (1 / 2 - 1 / Real.exp 1) ≤
        entropyPowerDelta (lambda * xA + (1 - lambda) * xB)) ∧
    (∀ lambda xA xB : ℝ, 0 ≤ lambda → lambda ≤ 1 → 1 ≤ xA → 1 ≤ xB →
      entropyPowerPhoton (lambda * xA + (1 - lambda) * xB) -
          lambda * entropyPowerPhoton xA - (1 - lambda) * entropyPowerPhoton xB =
        entropyPowerDelta (lambda * xA + (1 - lambda) * xB) -
          lambda * entropyPowerDelta xA - (1 - lambda) * entropyPowerDelta xB) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P11

end
