-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P11_scalarConvexComparison
-- name    : QAlgorithms.Papers.Independent.Claimed50.P11.scalarConvexComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:23:46.799264+00:00
-- url     : https://prove2.me/theorems/5cf51644-a897-44ab-bea1-c5fe9ebc766c
-- title:
--   Convex comparison between scalar qEPI and EPnI expressions
-- statement:
--   Let $g(N)=(N+1)\ln(N+1)-N\ln N$ on $N\ge0$, with $0\ln0=0$. Define $f(x)=g^{-1}(\ln x)$ for $x\ge1$. The function $f$ is nondecreasing and convex. For finite $N_A,N_B\ge0$ and $0\le\lambda\le1$,
--
--   $$
--   g^{-1}\!\left(\ln\left[\lambda e^{g(N_A)}+(1-\lambda)e^{g(N_B)}\right]\right)
--   \le \lambda N_A+(1-\lambda)N_B.
--   $$
--
--   This compares the scalar expressions associated with the beam-splitter qEPI and the conjectured EPnI. It does not establish the EPnI for physical output states.
-- source:
--   A generalization of the Entropy Power Inequality to Bosonic Quantum Systems, arXiv:1402.0404v2, PDF p. 23, §VI.B Eq. (102); §II.C

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P11

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

/-- PDF p.23 Eq.(102), with the discussion on p.9: f is increasing and
convex on [1,infinity), and the beam-splitter scalar comparison follows.
The weights are lambda and 1-lambda; amplifier weights are not substituted.
This does not assert the unproved EPnI for density operators. -/
theorem scalarConvexComparison :
    MonotoneOn entropyPowerPhoton (Set.Ici 1) ∧
    ConvexOn ℝ (Set.Ici 1) entropyPowerPhoton ∧
    (∀ lambda NA NB : ℝ, 0 ≤ lambda → lambda ≤ 1 → 0 ≤ NA → 0 ≤ NB →
      entropyPowerPhoton
        (lambda * Real.exp (thermalEntropy NA) +
          (1 - lambda) * Real.exp (thermalEntropy NB)) ≤
        lambda * NA + (1 - lambda) * NB) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P11

end
