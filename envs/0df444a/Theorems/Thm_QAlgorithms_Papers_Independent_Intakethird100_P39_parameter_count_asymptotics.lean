-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_parameter_count_asymptotics
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.parameter_count_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:44:35.903944+00:00
-- url     : https://prove2.me/theorems/77926485-7198-4393-81f8-b7247e1c5afd
-- title:
--   Asymptotics of parameter-count lower envelopes
-- statement:
--   For $m=2,10$, set $s=\lfloor n/m\rfloor$, $D_m=4^m-2\cdot4^{m/2}+1$, and $A_m(n)=4^n+1-2\cdot4^{m/2}-s(4^m-1)$. Let $G_m(n)=s+\lceil A_m(n)/D_m\rceil$ and $L_m(n)=1+\lceil A_m(n)/(sD_m)\rceil$ be the balanced lower-envelope expressions in Eqs. (11)-(12). Their limits as $n\to\infty$ are
--
--   $$\frac{G_2(n)}{4^n}\to\frac19,\quad\frac{G_{10}(n)}{4^n}\to\frac1{1046529},\quad\frac{nL_2(n)}{4^n}\to\frac29,\quad\frac{nL_{10}(n)}{4^n}\to\frac{10}{1046529},$$
--   $$\frac{G_{10}(n)}{G_2(n)}\to\frac1{116281},\qquad\frac{L_{10}(n)}{L_2(n)}\to\frac5{116281}.$$
--
--   These are asymptotics of parameter-count thresholds, not achieved synthesis costs. The source rounds the last ratio to $1/23256$; a physical duration ratio additionally includes the ratio of single-module durations. Eventual positive $s$ removes any relevance of the totalized expression at small $n$.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 5, Asymptotics of the parameter-count bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.5: the four lower-envelope asymptotics and both ratios.
The exact slot ratio is 5/116281; the printed 1/23256 is rounded.
These are parameter-count expressions, with no achieved physical speed-up. -/
theorem parameter_count_asymptotics :
    Filter.Tendsto (fun n : ℕ => (marginalGateBound n 2 : ℝ) / (4 : ℝ) ^ n)
      Filter.atTop (nhds (1 / 9 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (marginalGateBound n 10 : ℝ) / (4 : ℝ) ^ n)
      Filter.atTop (nhds (1 / 1046529 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (marginalSlotBound n 2 : ℝ) * n / (4 : ℝ) ^ n)
      Filter.atTop (nhds (2 / 9 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (marginalSlotBound n 10 : ℝ) * n / (4 : ℝ) ^ n)
      Filter.atTop (nhds (10 / 1046529 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (marginalGateBound n 10 : ℝ) /
      (marginalGateBound n 2 : ℝ)) Filter.atTop (nhds (1 / 116281 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (marginalSlotBound n 10 : ℝ) /
      (marginalSlotBound n 2 : ℝ)) Filter.atTop (nhds (5 / 116281 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
