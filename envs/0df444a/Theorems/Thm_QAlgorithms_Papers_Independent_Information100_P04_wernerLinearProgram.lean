-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_wernerLinearProgram
-- name    : QAlgorithms.Papers.Independent.Information100.P04.wernerLinearProgram
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:35:03.871195+00:00
-- url     : https://prove2.me/theorems/17900ac8-4d07-4858-9d09-1adc7421000d
-- title:
--   Exact finite Werner LP and attainable sparse optimum
-- statement:
--   Fix integers $d\ge2$, $m\ge1$ and $p\in[0,1]$. Let $r_i=\binom mi p^i(1-p)^{m-i}$, for $0\le i\le m$. Define $C_m[k,i]=2^{-m}\sum_l(-1)^l(d-1)^l(d+1)^{k-l}\binom kl\binom{m-k}{i-l}$, with out-of-range binomial coefficients zero. Let $\mathcal V_m$ be the set of all nonzero vertices of $\{v\ge0:|C_mv|\le\mathbf1\}$. Then
--
--   $$\frac{L(\rho_p^{\otimes m})}{m}=\max_{\lambda_v\ge0,\ \sum_v\lambda_vv=\mathbf1}\frac1m\sum_{v\in\mathcal V_m}\lambda_v(r\cdot v)\log_2(r\cdot v).$$
--
--   The maximum is attained using at most $m+1$ columns. The formulation allows every nonzero vertex, and every exactly feasible finite set of such columns yields a value at most $E_{d,\mathrm{PPT}}(\rho_p)$. The running maxima of the normalized positive-block levels converge to this operational rate. This gives exact finite-level optimality when all vertices are available, and lower certificates from feasible subsets, without a convergence-speed claim.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 29, eq134

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(134), PDF p.29: equality with the ALL-vertex LP and attainment with at most m+1
columns. Any exactly feasible finite column set is a lower certificate; running maxima converge. -/
theorem wernerLinearProgram (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    (∃ k : ℕ, k ≤ m+1 ∧ ∃ lam : Fin k → ℝ, ∃ v : Fin k → Fin (m+1) → ℝ,
      LPFeasible d m k lam v ∧
      LPObjective p m k lam v = L (copies (werner d p) m) / m ∧
      ∀ j : ℕ, ∀ weights : Fin j → ℝ, ∀ columns : Fin j → Fin (m+1) → ℝ,
        LPFeasible d m j weights columns →
          LPObjective p m j weights columns ≤ LPObjective p m k lam v) ∧
    (∀ j : ℕ, ∀ weights : Fin j → ℝ, ∀ columns : Fin j → Fin (m+1) → ℝ,
      LPFeasible d m j weights columns →
        LPObjective p m j weights columns ≤ distillable (werner d p)) ∧
    Tendsto (runningLevel (werner d p)) atTop (nhds (distillable (werner d p))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
