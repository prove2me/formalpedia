-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_table_analytical_optima
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.table_analytical_optima
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:30:53.969098+00:00
-- url     : https://prove2.me/theorems/db42db4e-496f-483c-8615-144ac58fa616
-- title:
--   Analytical finite-use optimal success probabilities
-- statement:
--   For each of the parallel, adaptive, and general process-matrix classes, let $P_{\mathcal C}(d,k)$ denote the greatest attainable constant success probability for a fixed universal heralded process that inverts every unknown $U\in SU(d)$ exactly using $k$ forward calls. Success means $p$ times the inverse channel, also on reference-entangled inputs. Then
--
--   $$P_{\mathcal C}(2,1)=\frac14,\qquad P_{\mathcal C}(3,1)=0\quad\text{for all three classes},$$
--   $$P_{\mathrm{parallel}}(2,2)=\frac25,\qquad P_{\mathrm{parallel}}(2,3)=\frac12.$$
--
--   Each value is attained and bounds every feasible protocol in its class. Memory, fixed channels, and measurements are free; only forward uses of the unknown unitary are counted.
--
--   These are exactly the analytical blue cells of Table I. The black $d=3,k=2$ entries are not included.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 4, Table I, blue cells

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.4, Table I: exactly the blue analytical cells; IsGreatest supplies both
an attaining protocol and the upper bound against every protocol in that class.
The black d=3,k=2 entry 1/9 is deliberately excluded. -/
theorem table_analytical_optima :
    (∀ c : CircuitClass, IsGreatest {p : ℝ | Attainable c 2 1 p} (1/4)) ∧
    IsGreatest {p : ℝ | Attainable .parallel 2 2 p} (2/5) ∧
    IsGreatest {p : ℝ | Attainable .parallel 2 3 p} (1/2) ∧
    (∀ c : CircuitClass, IsGreatest {p : ℝ | Attainable c 3 1 p} 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
