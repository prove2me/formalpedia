-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P11_vacuumLoss_entropyLowerBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P11.vacuumLoss_entropyLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:24:55.79804+00:00
-- url     : https://prove2.me/theorems/efbdb052-78be-43ed-967a-4db997d590db
-- title:
--   Fixed-vacuum pure-loss output entropy lower bound
-- statement:
--   Let $0\le\lambda\le1$ and let $\rho$ be any positive trace-class density of trace one on the full single-mode Fock space $\ell^2(\mathbb N)$. Suppose its von Neumann entropy in nats is the finite value $\bar S>0$. Let $\mathcal L_\lambda(\rho)$ be its vacuum pure-loss output, constructed by the accepted attenuator coefficients with amplitude $\sqrt\lambda$. The coefficient Kraus series converges absolutely and yields a normalized positive trace-class density, and $$S(\mathcal L_\lambda(\rho))\ge\ln(\lambda e^{\bar S}+1-\lambda).$$ No finite-energy, Gaussian or finite-rank restriction is imposed. Both transmissivity endpoints are included; output entropy is extended nonnegative entropy.
-- source:
--   A generalization of the Entropy Power Inequality to Bosonic Quantum Systems, arXiv:1402.0404v2, PDF p. 10, §II.D Eq. (37)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P11

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

/-- PDF p.10, Eq.(37): single-mode minimum-output-entropy lower bound with
fixed vacuum environment and finite input entropy Sbar>0, in nats.
The input is an arbitrary normalized full-Fock density, with no energy,
Gaussianity or rank assumption. The output is constructed by the accepted
attenuator coefficients. Its summability and density properties are included
as channel-model guarantees, not assumed. Both lambda endpoints are retained.
This is the printed lower bound, not the conjectured thermal minimizer. -/
theorem vacuumLoss_entropyLowerBound (lambda Sbar : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda ≤ 1) (hSbar : 0 < Sbar)
    (rho : State ℕ)
    (hentropy : extendedEntropyNats rho.coefficients = ENNReal.ofReal Sbar) :
    (∀ i j : ℕ, Summable (vacuumLossSummand lambda rho.coefficients i j)) ∧
    IsDensity (vacuumLossOutput lambda rho.coefficients) ∧
    ENNReal.ofReal (Real.log (lambda * Real.exp Sbar + (1 - lambda))) ≤
      extendedEntropyNats (vacuumLossOutput lambda rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P11

end
