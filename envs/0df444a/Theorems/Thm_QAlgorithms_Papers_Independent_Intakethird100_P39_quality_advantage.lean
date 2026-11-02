-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_quality_advantage
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.quality_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:45:45.275221+00:00
-- url     : https://prove2.me/theorems/fbb01ad0-9127-460e-9435-ef21453b2d75
-- title:
--   Advantage criterion in the independent-error quality model
-- statement:
--   Let $r,r'\in\mathbb N$ with $r'\le r$, let $F_2,F_m\in[-1,1]$ be trace fidelities, let $\tau_2,\tau_m\ge0$, and let $T_R>0$. In the assumed independent-error and scalar-relaxation model, define $q(F,T)=F e^{-T/T_R}$. The direct module has greater quality than a decomposition with $r$ occurrences and $r'$ sequential slots precisely when
--
--   $$F_m>F_2^r\exp\!\left(-\frac{r'\tau_2-\tau_m}{T_R}\right)\quad\Longleftrightarrow\quad q(F_m,\tau_m)>q(F_2^r,r'\tau_2).$$
--
--   When relaxation is suppressed the criterion is $F_m>F_2^r$. This is a scalar comparison within the stated model, not an assertion of independent propagation for arbitrary coherent errors.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 6, Advantage criterion in the independent-error quality model, Eq. (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF pp.5-6, Eq. (15): an equivalent advantage criterion inside the
independent-error quality model. Fidelity counts r occurrences, relaxation
counts rprime sequential slots. The second clause suppresses relaxation. -/
theorem quality_advantage (r rprime : ℕ) (hr : rprime ≤ r)
    (F2 Fm tau2 taum TR : ℝ)
    (hF2 : F2 ∈ Set.Icc (-1) 1) (hFm : Fm ∈ Set.Icc (-1) 1) (hTR : 0 < TR)
    (htau2 : 0 ≤ tau2) (htaum : 0 ≤ taum) :
    (Fm > F2 ^ r * Real.exp (-((rprime : ℝ) * tau2 - taum) / TR) ↔
      quality Fm taum TR > quality (F2 ^ r) ((rprime : ℝ) * tau2) TR) ∧
    (quality Fm 0 TR > quality (F2 ^ r) 0 TR ↔ Fm > F2 ^ r) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
