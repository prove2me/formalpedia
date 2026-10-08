-- Prove2me | Theorems.Thm_WeakMFG_Existence_optimal_set_7_4
-- name    : WeakMFG.Existence.optimal_set_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:16:09.16898+00:00
-- url     : https://prove2.me/theorems/50717ec6-1143-4c0d-9651-dbfb6de5caee
-- title:
--   §7, (7.1)–(7.4) and Remark 7.2 — 𝔸(µ, ν) is nonempty and consists of optimal controls, with E[Y^{µ,ν}_0] = J^{µ,ν}(α)
-- statement:
--   Assume the standing assumptions (S), with $A\neq\emptyset$. Let $\mu\in\mathcal P_\psi(\mathcal C)$, $\nu\in\mathcal M$, and let $(Y^{\mu,\nu},Z^{\mu,\nu})$ solve the BSDE
--   $$Y^{\mu,\nu}_t=g(X,\mu)+\int_t^TH(s,X,\mu,\nu_s,Z^{\mu,\nu}_s)\,ds-\int_t^TZ^{\mu,\nu}_s\,dW_s.\tag{7.1}$$
--   Let $\mathbb A(\mu,\nu)=\{\alpha\in\mathbb A:\alpha_t\in A(t,X,\mu,Z^{\mu,\nu}_t)\ dt\times dP\text{-a.e.}\}$ (7.4). Then:
--
--   1. $\mathbb A(\mu,\nu)$ is nonempty (Remark 7.2);
--   2. every $\alpha\in\mathbb A(\mu,\nu)$ is an optimal control: $J^{\mu,\nu}(\beta)\le J^{\mu,\nu}(\alpha)$ for every $\beta\in\mathbb A$, i.e. $V^{\mu,\nu}=J^{\mu,\nu}(\alpha)$;
--   3. for every $\alpha\in\mathbb A(\mu,\nu)$, $\mathbb E[Y^{\mu,\nu}_0]=J^{\mu,\nu}(\alpha)$.
--
--   This reduces the search for a mean field game solution to a fixed point of $(\mu,\nu)\mapsto\Phi(\mu,\mathbb A(\mu,\nu))$.
--
--   **Formalization Note** The solution of (7.1) is a hypothesis, not a choice. The set (7.4) is formed at an arbitrary $q_0\in\mathcal P(A)$ (by (S.5) it does not depend on it). Each control has a version of its density, and the comparisons hold for all versions. Two hypotheses are added and disclosed. $A\neq\emptyset$ is needed: otherwise $\mathbb A=\emptyset$, and the page uses it ("$A(t,x,\mu,z)$ is always nonempty"). Joint measurability of $f$ in $(t,x,q,a)$ makes the extension $\int\nu_t(dq)f(t,X,\mu,q,a)$ measurable, which the page presupposes when it writes the extension as an integral (p. 21).
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7, pp. 21–22, (7.1)–(7.4) and Remark 7.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward
import Definitions.Def_WeakMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- §7, pp. 21–22 ((7.1)–(7.4)) and Remark 7.2 (Carmona–Lacker, arXiv:1307.1152v2): under the
standing assumptions only, for `μ ∈ P_ψ(C)`, `ν ∈ M` and the solution `(Y^{μ,ν}, Z^{μ,ν})` of the
BSDE (7.1), (a) the set `𝔸(μ, ν)` of (7.4) is nonempty; (b) every `α ∈ 𝔸(μ, ν)` is an optimal
control, `J^{μ,ν}(β) ≤ J^{μ,ν}(α)` for every `β ∈ 𝔸`; (c) `E[Y^{μ,ν}_0] = J^{μ,ν}(α) = V^{μ,ν}`.
Formalization Notes: `A` nonempty (as in the goal); D5 (`JointProg`), which makes the extension
`f(t, x, μ, ν, a) = ∫ ν(dq) f(t, x, μ, q, a)` measurable; the BSDE solution is a hypothesis, not a
choice; the maximizer set is evaluated at an arbitrary `q₀` (by (S.5) it does not depend on it). -/
theorem optimal_set_7_4 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp)
    (hA : A.Nonempty) (hD5 : JointProg A f)
    (μ : Ppsi ψ) (ν : Mflow A) (Y : ℝ≥0 → Ω → Unit → ℝ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (hYZ : IsBSDE71 B σ b f g Xp μ ν Y Z) (q₀ : PA A) :
    (Aopt B σ b f Xp μ Z q₀).Nonempty ∧
    ∀ α ∈ Aopt B σ b f Xp μ Z q₀,
      (∃ D, IsDensity B σ b Xp μ α D) ∧
      (∀ β : ℝ≥0 → Ω → EA, IsAdmissible B A β →
        ∀ Dα Dβ : Ω → ℝ, IsDensity B σ b Xp μ α Dα → IsDensity B σ b Xp μ β Dβ →
          JrewNu B f g Xp μ ν β Dβ ≤ JrewNu B f g Xp μ ν α Dα) ∧
      (∀ Dα : Ω → ℝ, IsDensity B σ b Xp μ α Dα →
        ∫ ω, Y 0 ω () ∂B.P = JrewNu B f g Xp μ ν α Dα) := by sorry

end WeakMFG.Existence
