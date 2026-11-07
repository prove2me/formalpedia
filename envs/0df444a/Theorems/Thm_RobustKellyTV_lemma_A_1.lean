-- Prove2me | Theorems.Thm_RobustKellyTV_lemma_A_1
-- name    : RobustKellyTV.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:31.34454+00:00
-- url     : https://prove2.me/theorems/cd7bc8f9-4f08-474a-b091-ac2854dedab3
-- title:
--   Lemma A.1 — continuity of $a,b,E_U,\Gamma$ on $K_{m,\delta}$ and $m/\max_iP_i\le E_U(i)\le1/\min_iP_i$
-- statement:
--   Assume the standing assumptions. For $m,\delta>0$ let
--
--   $$K_{m,\delta}=\{U\in\Delta_d:\ \min_iU_i\ge m,\ D_{\mathrm{TV}}(U,P)\ge\epsilon_0+\delta\}.$$
--
--   On $K_{m,\delta}$ the maps $U\mapsto a(U)$, $U\mapsto b(U)$, $U\mapsto E_U$ and $U\mapsto\Gamma(U)$ are continuous, and
--
--   $$\frac{m}{\max_iP_i}\le E_U(i)\le\frac1{\min_iP_i}\qquad(U\in K_{m,\delta},\ i\le d).$$
--
--   This regularity is used to transfer accuracy of the predictor to accuracy of the bet.
--
--   Differences from the source:
--   - encoding: on every nonempty K_{m,δ} → on K_{m,δ}, without the nonemptiness hypothesis; reason: on the empty set every clause holds trivially, so no instance changes
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, Appendix A.1, display before Lemma A.1 and Lemma A.1, p.22

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

/-- **Lemma A.1** (Continuity and uniform boundedness). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Lemma A.1, p.22.

For `m, δ > 0` let `K_{m,δ} = {U ∈ ∆_d : minᵢ Uᵢ ≥ m, D_TV(U, P) ≥ ϵ0 + δ}`. On every nonempty
`K_{m,δ}` the maps `U ↦ a(U)`, `U ↦ b(U)`, `U ↦ E_U` and `U ↦ Γ(U)` are continuous, and
`m / maxᵢ Pᵢ ≤ E_U(i) ≤ 1 / minᵢ Pᵢ` uniformly over `U ∈ K_{m,δ}` and `i ≤ d`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. The nonemptiness hypothesis is dropped: continuity on the empty set
and the bounds over it hold trivially, so the statement is the same. `minᵢ Uᵢ ≥ m` is
`∀ i, m ≤ Uᵢ`. `E_U` is continuous as a map into `Fin d → ℝ` (product topology). -/
theorem lemma_A_1 {d : ℕ} (σ : Setting d) (m δ : ℝ) (hm : 0 < m) (hδ : 0 < δ) :
    ContinuousOn (lowerThr σ)
        {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P} ∧
      ContinuousOn (upperThr σ)
        {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P} ∧
      ContinuousOn (oracleE σ)
        {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P} ∧
      ContinuousOn (Gamma σ)
        {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P} ∧
      ∀ U ∈ {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P}, ∀ i,
        m / Pmax σ ≤ oracleE σ U i ∧ oracleE σ U i ≤ 1 / Pmin σ := by sorry

end RobustKellyTV
