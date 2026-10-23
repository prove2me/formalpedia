-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_anomaly_coheringPower_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P41.anomaly_coheringPower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:24:02.32385+00:00
-- url     : https://prove2.me/theorems/35d40bfe-636b-4456-8175-673fe9addfe7
-- title:
--   Anomaly bounded by output coherence and cohering power
-- statement:
--   Let $d\ge1$, let $\rho$ be a positive semidefinite trace-one matrix on $\mathbb C^d$, and let $\mathcal E$ be a CPTP map on that matrix algebra. Fix a complete orthonormal reference basis, let $D$ be its dephasing map, and put $R=\mathcal E(\rho)$ and $T=\mathcal E(D\rho)$. Assume every reference population $R_{xx}$ is strictly positive. Write $p_{\min}=\min_x R_{xx}$, $S(X)=-\operatorname{Tr}(X\ln X)$ with $0\ln0=0$, $C(X)=S(DX)-S(X)$, and $P(\mathcal E)=\max_{\omega\text{ density},D\omega=\omega}C(\mathcal E(\omega))$. The complex trace anomaly $A_C=\operatorname{Tr}((DR)^{-1}(R-DR)T)$ satisfies
--
--   $$|A_C|\le\frac{2\sqrt{C(R)P(\mathcal E)}}{p_{\min}}.$$
--
--   This bounds the overlap defining the anomaly by output coherence and the channel's ability to generate coherence.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 2, Eq.(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.2, Eq.(5): anomaly bound; the factor 2 is outside the square root. -/
theorem anomaly_coheringPower_bound {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hfinal : ∀ x : Fin d, 0 < ((E rho) x x).re) :
    ‖anomaly E rho‖ ≤
      2 * Real.sqrt (coherence (E rho) * coheringPower E) / minPopulation (E rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
