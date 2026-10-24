-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_regularization_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.regularization_limit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:54:28.323928+00:00
-- url     : https://prove2.me/theorems/5d35553b-e053-4849-8f27-8478707751fc
-- title:
--   Existence of the formation regularization
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   Write $E_f(\tau)$ for the minimum, over all finite ensembles $\tau=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ with $p_i\ge0$, $\sum_i p_i=1$ and unit vectors $\psi_i$, of $\sum_i p_i S(\operatorname{Tr}_B|\psi_i\rangle\langle\psi_i|)$. Here $S$ is von Neumann entropy with base-two logarithms and $0\log 0=0$, so entanglement is measured in ebits.
--
--   There is a finite real limit, equal to the infimum of the positive-copy quotients:
--
--   $$\lim_{n\to\infty}\frac{E_f(\rho^{\otimes n})}{n}=E_f^\infty(\rho)=\inf_{n\ge1}\frac{E_f(\rho^{\otimes n})}{n}\in\mathbb R.$$
--
--   This gives a well-defined regularized formation value for the operational statements.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 3, Paragraph after Eq.(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.3, paragraph after Eq.(8): existence of the formation regularization.
The infimum representative is identified with a genuine finite real limit. -/
theorem regularization_limit {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    Filter.Tendsto (formationSequence rho) Filter.atTop
      (nhds (regularizedFormation rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
