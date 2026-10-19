-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_conicAttainmentDuality
-- name    : QAlgorithms.Papers.Independent.Information100.P21.conicAttainmentDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:03:51.78442+00:00
-- url     : https://prove2.me/theorems/1daccdfb-832c-43b7-8d52-623b5dd78b48
-- title:
--   I.C–D — exact conic/SDP formulations, attainment and duality
-- statement:
--   For every two-qubit state $\rho$, both conic feasible sets are nonempty and their costs bounded below. The exact formulations are
--   $$R_g=\min_{Y\succeq0,\ \rho^\Gamma+Y^\Gamma\succeq0}\operatorname{Tr}Y,\qquad R_s=\min_{K\succeq0,\ K^\Gamma\succeq0,\ \rho^\Gamma+K\succeq0}\operatorname{Tr}K.$$
--   Both primal minima and dual maxima are attained, with no gap within either primal-dual pair. The generalized dual has $W\succeq0$, $I-W^\Gamma\succeq0$; the standard dual has $W,P,Q\succeq0$, $I-W=P+Q^\Gamma$. Both maximize $-\operatorname{Tr}(W\rho^\Gamma)$. The statement identifies primal feasibility with the actual separable cone in two qubits.
--
--   PDF p.6, S16: retain strict feasibility of tI above max(0,-lambdaMin). The least eigenvalue is computed from the real spectrum of the actual partial transpose, with attainment concluded.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 5, I.C–D — exact conic/SDP formulations, attainment and duality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 5, exact conic/SDP formulations, attainment and duality.
Round-one coverage restoration: PDF p.6, S16: retain strict feasibility of tI above max(0,-lambdaMin). The least eigenvalue is computed from the real spectrum of the actual partial transpose, with attainment concluded. -/
theorem conicAttainmentDuality (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) :
  Set.Nonempty {Y : Op QQ | primalG rho Y} ∧
  Set.Nonempty {Y : Op QQ | primalS rho Y} ∧
  BddBelow {s : ℝ | ∃ Y : Op QQ, primalG rho Y ∧ s=Y.trace.re} ∧
  BddBelow {s : ℝ | ∃ Y : Op QQ, primalS rho Y ∧ s=Y.trace.re} ∧
  rg rho=sInf {s : ℝ | ∃ Y : Op QQ, primalG rho Y ∧ s=Y.trace.re} ∧
  rs rho=sInf {s : ℝ | ∃ K : Op QQ, K.PosSemidef ∧ (pt K).PosSemidef ∧
    (pt rho+K).PosSemidef ∧ s=K.trace.re} ∧
  (∃ Y : Op QQ, optG rho Y) ∧ (∃ Y : Op QQ, optS rho Y) ∧
  (∃ W : Op QQ, optDG rho W ∧ (-(W * pt rho).trace.re)=rg rho) ∧
  (∃ W P Q : Op QQ, optDS rho W P Q ∧ (-(W * pt rho).trace.re)=rs rho) ∧
  (∀ Y : Op QQ, primalG rho Y ↔ Y.PosSemidef ∧
    QAlgorithms.Entanglement.IsSeparablePositive (rho+Y)) ∧
  (∀ K : Op QQ, (K.PosSemidef ∧ (pt K).PosSemidef ∧ (pt rho+K).PosSemidef) ↔
    QAlgorithms.Entanglement.IsSeparablePositive (pt K) ∧
    QAlgorithms.Entanglement.IsSeparablePositive (rho+pt K)) ∧
  (let eigenvalues : Set ℝ := {q | ∃ v : QQ → ℂ, v ≠ 0 ∧
      (pt rho).mulVec v = (q : ℂ) • v}
   let lambdaMin := sInf eigenvalues
   IsLeast eigenvalues lambdaMin ∧
   ∀ t : ℝ, max 0 (-lambdaMin) < t →
     ((t : ℂ) • (1 : Op QQ)).PosDef ∧
     (pt rho + pt ((t : ℂ) • (1 : Op QQ))).PosDef ∧
     (pt ((t : ℂ) • (1 : Op QQ))).PosDef) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
