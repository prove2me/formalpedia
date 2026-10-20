-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_activeSupportRepair
-- name    : QAlgorithms.Papers.Independent.Information100.P76.activeSupportRepair
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:59:08.495404+00:00
-- url     : https://prove2.me/theorems/647a561e-5429-47cd-97c1-29b763b8c291
-- title:
--   Theorem 4.1: active support repair, exactification and equality of intrinsic costs
-- statement:
--   Fix a square CPTP channel $\Phi$ on a positive $q$-dimensional space. Let $k=\operatorname{rank}J_\Phi$ for its normalized Choi state and let $\mu$ be the smallest strictly positive eigenvalue of $J_\Phi$. There are constants $\eta_0,B>0$ and a nonnegative modulus $\varepsilon_\eta\to0$, chosen before the arbitrary finite collision, with $\varepsilon_\eta\le\min(1,B\eta^{1/6})$ for $0<\eta<\eta_0$. Every collision $C=(U,\tau)$ on $R$ bath dimensions satisfying $D_\diamond(\Phi_C,\Phi)\le\eta$ has a repaired collision $\widehat C$ and a further exact collision $C_{\rm ex}$ such that
--
--   $$\begin{gathered}\widehat R=(k+1)R,\quad\operatorname{spec}_+(\widehat\tau)=\operatorname{spec}_+(\tau),\quad\operatorname{supp}J_{\Phi_{\widehat C}}\subseteq\operatorname{supp}J_\Phi,\\D_\diamond(\Phi_{\widehat C},\Phi)\le\eta+\varepsilon_\eta,\quad g_{\widehat C}\le g_C+\beta_q(\varepsilon_\eta),\\R_{\rm ex}\le(k+1)R+k,\quad\Phi_{C_{\rm ex}}=\Phi,\quad g_{C_{\rm ex}}\le g_C+\beta_q(\varepsilon_\eta)+f\log_2k.\end{gathered}$$
--
--   Here $\beta_q(e)=4e\log_2q+(1+e)H_2(e/(1+e))$ and $f=2(\eta+\varepsilon_\eta)/(\mu+2(\eta+\varepsilon_\eta))$. The exactifier has $S(\tau_{\rm ex})=H_2(f)+(1-f)S(\tau)$, so spectrum preservation is claimed only for support repair. Moreover $\kappa_{\rm exact}(\Phi)=\kappa(\Phi)$. The thresholds and gain penalties are uniform in $R$, $\tau$, and any auxiliary dimension. This is the repair result needed to pass from approximate to exact finite witnesses.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 7, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF pp.7–9, Theorem 4.1: active support repair preserves the old positive spectrum;
the further flagged exactification has its own explicitly changed entropy. All moduli and
thresholds are chosen before the arbitrary finite bath and initializer. -/
theorem activeSupportRepair {q : ℕ} (hq : 0 < q)
    (Phi : Superop (Fin q) (Fin q)) (hPhi : IsChannel Phi) :
    exactCollisionCost Phi = intrinsicCost Phi ∧
    ∃ eta0 B : ℝ, 0 < eta0 ∧ 0 < B ∧ ∃ epsilon : ℝ → ℝ,
      Tendsto epsilon (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ eta : ℝ, 0 < eta → eta < eta0 →
        0 ≤ epsilon eta ∧ epsilon eta ≤ 1 ∧ epsilon eta ≤ B * eta ^ (1 / 6 : ℝ) ∧
        ∀ C : Collision q, channelDistance (collisionChannel C) Phi ≤ eta →
          ∃ repaired exact : Collision q,
            repaired.R = (Matrix.rank (choi Phi) + 1) * C.R ∧
            samePositiveSpectrum C.tau repaired.tau ∧
            choiSupportContained (collisionChannel repaired) Phi ∧
            channelDistance (collisionChannel repaired) Phi ≤ eta + epsilon eta ∧
            collisionGain repaired ≤ collisionGain C + repairModulus q (epsilon eta) ∧
            exact.R ≤ (Matrix.rank (choi Phi) + 1) * C.R + Matrix.rank (choi Phi) ∧
            collisionChannel exact = Phi ∧
            let f := 2 * (eta + epsilon eta) /
              (minPositiveEigenvalue (choi Phi) + 2 * (eta + epsilon eta))
            collisionGain exact ≤ collisionGain C + repairModulus q (epsilon eta) +
              f * Real.logb 2 (Matrix.rank (choi Phi)) ∧
            vnEntropy exact.tau = binEntropy2 f + (1 - f) * vnEntropy C.tau := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
