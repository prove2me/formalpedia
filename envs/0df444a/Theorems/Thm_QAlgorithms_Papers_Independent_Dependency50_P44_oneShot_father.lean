-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_oneShot_father
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.oneShot_father
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:26:53.358282+00:00
-- url     : https://prove2.me/theorems/255d08c3-7535-42de-ab7a-ffa0e386a3dc
-- title:
--   Finite one-shot broadcast father error bound
-- statement:
--   Let $\mathcal N:A'\to B_1B_2$ have a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$ on finite-dimensional nonzero complex spaces with fixed bases. Take message/reference dimensions $|A_i|=|R_i|=|\bar B_i|$, assistance dimensions $|\widetilde A_i|=|\widetilde B_i|$, and retrieved-pair dimensions $|\breve A_1|=|\breve B_1|$. Let
--
--   $$\varphi=\Phi^{R_1A_1}\otimes\Phi^{\widetilde A_1\widetilde B_1}\otimes\Phi^{R_2A_2}\otimes\Phi^{\widetilde A_2\widetilde B_2},\qquad |\Phi\rangle=|S|^{-1/2}\sum_{i=1}^{|S|}|ii\rangle.$$
--
--   For every encoding isometry $W:A_1\widetilde A_1A_2\widetilde A_2\to A'\breve A_1\widehat A$, compute $\psi=U_{\mathcal N}W\varphi$. Put $S_1=R_2\widetilde B_2 B_2E\widehat A$, $T_1=R_1\widetilde B_1\breve A_1S_1$, $S_2=R_1\widetilde B_1\breve A_1B_1E\widehat A$, and $T_2=R_2\widetilde B_2S_2$, and define
--
--   $$d_1(\rho)=\left[\frac{|R_1||\widetilde B_1||\breve A_1|\operatorname{rank}(\rho^{S_1})}{|\widetilde B_1|^2}\operatorname{Tr}((\rho^{T_1})^2)\right]^{1/4},\qquad
--   d_2(\rho)=\left[\frac{|R_2||\widetilde B_2|\operatorname{rank}(\rho^{S_2})}{|\widetilde B_2|^2}\operatorname{Tr}((\rho^{T_2})^2)\right]^{1/4}.$$
--
--   There exist an encoding isometry $U$ with the same domain and codomain as $W$, local decoding isometries $V_1:B_1\widetilde B_1\to\bar B_1\widehat B_1\breve B_1$ and $V_2:B_2\widetilde B_2\to\bar B_2\widehat B_2$, arbitrary sufficiently large decoder garbage spaces, and a normalized pure state $\widehat\psi^{\widehat B_1\widehat B_2E\widehat A}$, such that for every pair of normalized comparison density operators $\rho_1,\rho_2$ on the entire system of $\psi$,
--
--   $$\left\|(V_2V_1U_{\mathcal N}U)\varphi(V_2V_1U_{\mathcal N}U)^\dagger-\widehat\psi\otimes\Phi^{\breve A_1\breve B_1}\otimes\Phi^{R_1\bar B_1}\otimes\Phi^{R_2\bar B_2}\right\|_1
--   \le4d_1(\rho_1)+2d_2(\rho_2)+2\|\psi-\rho_1\|_1+\|\psi-\rho_2\|_1.$$
--
--   All vectors inside density expressions denote their pure density operators, and local actions include identities on untouched factors. This is a finite one-shot bound, with all three EPR target factors. The uniform order over comparison states is retained exactly as printed, even though the proof's selection appears state-dependent; the subnormalized comparison extension used later is not asserted.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 3, Theorem 1 / Eq. (4), continued on p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF pp.3–4, Theorem 1, (4): every encoding isometry W has replacement encoder and local
isometries with the printed one-shot bound, uniformly over all NORMALIZED comparison states.
The quantifiers are kept as printed: forall W, exists U,V1,V2, forall rho1,rho2. The proof's
choice of random unitaries depends on the comparison states; this mismatch needs independent
moderation. No subnormalized extension used later in VI is silently asserted here. -/
theorem oneShot_father {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b)
    (P : ShotDimensions) (W : Matrix (ShotEncoded P a) (ShotInput P) ℂ)
    (hW : Wᴴ * W = 1) :
    ∃ (U : Matrix (ShotEncoded P a) (ShotInput P) ℂ) (g1 g2 : ℕ)
      (V1 : ShotDecoder1 P b g1) (V2 : ShotDecoder2 P b g2)
      (eta : EuclideanSpace ℂ (ShotGarbageBasis P g1 g2 N.environment)),
      Uᴴ * U = 1 ∧ V1ᴴ * V1 = 1 ∧ V2ᴴ * V2 = 1 ∧ ‖eta‖ = 1 ∧
      ∀ (rho1 rho2 : Operator (ShotBasis P b N.environment)),
        IsDensityMatrix rho1 → IsDensityMatrix rho2 →
        traceNorm (pureDensity (shotDecoded N P U V1 V2) - pureDensity (shotTarget P eta)) ≤
          shotErrorBound (pureDensity (shotVector N P W)) rho1 rho2 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
