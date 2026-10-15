-- Prove2me | Theorems.Thm_SuspensionContract_AlwaysWork_lemma_EC_3
-- name    : SuspensionContract.AlwaysWork.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:17.609298+00:00
-- url     : https://prove2.me/theorems/b2c2ed5a-2876-4c91-bd25-608264b24d3a
-- title:
--   Lemma EC.3, p. ec32 — ψ₁ is continuous and decreasing on [0, w̄], and ψ₁(θ̲) = K has a unique root θ̲_K ∈ (0, w̄), decreasing in K
-- statement:
--   Assume the standing assumptions, Condition 2 ($\mu<\rho-r$, $R\ge\hat R$) and $K\in(0,\bar K_2)$, where $\bar K_2=\bar V-\underline v-\bar w$. Let $\psi_1(\underline\theta)=\bar V-\underline v-\bar w-C^1(\underline\theta)\,\bar w^{\,r/\rho}$ with $C^1$ from (EC.67). Then:
--
--   1. $\psi_1$ is continuous and strictly decreasing on $[0,\bar w]$;
--   2. $\psi_1(\bar w)=0$ and $\psi_1(0)=\bar V-\underline v-\bar w>K$;
--   3. there is a unique $\underline\theta_K\in(0,\bar w)$ with $\psi_1(\underline\theta_K)=K$;
--   4. $K\mapsto\underline\theta_K$ is strictly decreasing on $(0,\bar K_2)$ and
--   $$\lim_{K\downarrow0}\underline\theta_K=\bar w.$$
--
--   Together with (EC.67), this produces the parameters $(c_K,m_K,\underline\theta_K)=(C^1(\underline\theta_K),m(\underline\theta_K),\underline\theta_K)$ of Lemma 5 and their monotonicity in $K$.
--
--   **Formalization Note.** $C^1(0)$ is Lean's value $0$ (from $0^{r/\rho-1}=0$ and $x/0=0$), which is the limit of $C^1$ at $0^+$ since $r<\rho$; the paper's continuity on $[0,\bar w]$ refers to this extension. In item 4, $\underline\theta_K$ is the function `thetaOf` (the infimum of the roots of $\psi_1=K$ in $(0,\bar w)$), and the limit is along $K\downarrow0$. "Decreasing" is read as strictly decreasing.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec32, Lemma EC.3

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting
import Definitions.Def_SuspensionContract_AlwaysWork_ValueFunctions

namespace SuspensionContract.AlwaysWork

open Filter Topology

/-- Lemma EC.3, p. ec32: under Condition 2 and `K ∈ (0, K̄₂)`, `ψ₁` is continuous and strictly
decreasing on `[0, w̄]`, `ψ₁(w̄) = 0`, `ψ₁(0) = V̄ − v̲ − w̄ > K`, `ψ₁(θ̲) = K` has a unique root
`θ̲_K ∈ (0, w̄)`; and `K ↦ θ̲_K` is strictly decreasing on `(0, K̄₂)` with `θ̲_K → w̄` as `K ↓ 0`. -/
theorem lemma_EC_3 (P : Params) (hP : P.Standing) (h2 : P.Condition2) (hK : P.K < P.Kbar2) :
    ContinuousOn P.psi1 (Set.Icc 0 P.wbar) ∧ StrictAntiOn P.psi1 (Set.Icc 0 P.wbar) ∧
      P.psi1 P.wbar = 0 ∧ P.psi1 0 = P.Vbar - P.vlow - P.wbar ∧
      P.K < P.Vbar - P.vlow - P.wbar ∧
      (∃! θ : ℝ, θ ∈ Set.Ioo 0 P.wbar ∧ P.psi1 θ = P.K) ∧
      StrictAntiOn P.thetaOf (Set.Ioo 0 P.Kbar2) ∧
      Tendsto P.thetaOf (𝓝[>] 0) (𝓝 P.wbar) := by sorry

end SuspensionContract.AlwaysWork
