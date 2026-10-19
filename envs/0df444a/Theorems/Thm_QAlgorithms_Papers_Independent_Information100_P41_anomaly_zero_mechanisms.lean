-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_anomaly_zero_mechanisms
-- name    : QAlgorithms.Papers.Independent.Information100.P41.anomaly_zero_mechanisms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:24:40.103069+00:00
-- url     : https://prove2.me/theorems/86aaf5b2-e793-4220-8a7d-56619bccdf43
-- title:
--   Two sufficient mechanisms for zero trace anomaly
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^d$, $d\ge1$, and let $\mathcal E$ be a CPTP map. In a fixed complete orthonormal reference basis, put $R=\mathcal E(\rho)$, $T=\mathcal E(D\rho)$ and assume all diagonal populations of $R$ are positive. Let $C(X)=S(DX)-S(X)$ use natural-log von Neumann entropy, and set $A_C=\operatorname{Tr}((DR)^{-1}(R-DR)T)$. Then
--
--   $$C(R)=0\ \Longrightarrow\ A_C=0,\qquad T=DT\ \Longrightarrow\ A_C=0.$$
--
--   Each condition is sufficient; these identities isolate two mechanisms that annihilate the trace anomaly.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 2, Anomaly-free mechanisms

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.2: two sufficient trace-anomaly-zero mechanisms, not necessity or an exponential FT. -/
theorem anomaly_zero_mechanisms {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hfinal : ∀ x : Fin d, 0 < ((E rho) x x).re) :
    (coherence (E rho) = 0 → anomaly E rho = 0) ∧
    (E (Matrix.diagonal (Matrix.diag rho)) =
      Matrix.diagonal (Matrix.diag (E (Matrix.diagonal (Matrix.diag rho)))) →
      anomaly E rho = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
