-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_theorem_3_8
-- name    : WiesemannRMDP.AffineSDP.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:06.439591+00:00
-- url     : https://prove2.me/theorems/7016b79c-1263-4560-85cc-23bffc54e6d4
-- title:
--   Theorem 3.8 — the affine reward-to-go SDP (20) is exact for L = 1 and a conservative approximation of (19) for L > 1
-- statement:
--   Consider the robust MDP with an affinely parametrized ambiguity set under its standing assumptions ($\Xi$ of the form (3b) with $O_l\preceq 0$, bounded, with a Slater point; $p^\xi(\cdot\mid s,a)\in\mathcal M(\mathcal S)$ on $\Xi$; $r\ge 0$; $\lambda\in(0,1)$; $p_0\in\mathcal M(\mathcal S)$), and fix a policy $\pi\in\Pi$. Compare the affine approximate policy evaluation problem
--   $$\sup_{\vartheta:\Xi\overset{a}{\mapsto}\mathbb R^S}\Big\{\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi) \;:\; \vartheta(\xi)\le\widehat r(\xi)+\lambda\widehat P(\xi)\vartheta(\xi)\ \ \forall\,\xi\in\Xi\Big\} \tag{19}$$
--   with the semidefinite program (20): maximize $\tau$ over $\tau\in\mathbb R$, $w\in\mathbb R^S$, $W\in\mathbb R^{S\times q}$, $\gamma\in\mathbb R^L_+$, $\Gamma\in\mathbb R^{S\times L}_+$ subject to the linear matrix inequalities (20b) and (20c).
--
--   Let $(\tau^*,w^*,W^*,\gamma^*,\Gamma^*)$ be an optimal solution of (20) and set $\vartheta^*(\xi):=w^*+W^*\xi$. Then:
--
--   1. **(a)** If $L=1$, (19) and (20) are equivalent: $\tau^*$ is the supremum of (19), attained, and $\vartheta^*$ is feasible and optimal in (19), with $\inf_{\xi\in\Xi}p_0^\top\vartheta^*(\xi)=\tau^*$.
--   2. **(b)** If $L>1$, (20) is a conservative approximation of (19): $\tau^*$ is a lower bound on the supremum of (19), $\vartheta^*$ is feasible in (19), and
--   $$\inf_{\xi\in\Xi}p_0^\top\vartheta^*(\xi)=\tau^*.$$
--
--   Since (19) restricts the policy evaluation problem (10) to affine reward to-go functions, $\tau^*$ is in either case a lower bound on the worst-case expected total reward of $\pi$, computable by semidefinite programming for an ambiguity set that need not be rectangular.
--
--   **Formalization Note.** Affine $\vartheta$ are encoded as $\vartheta(\xi)=w+W\xi$, the paper's own reformulation (21). "$\tau^*$ is the supremum of (19)" is stated as: $\tau^*$ is the greatest element of the set of objective values of feasible solutions of (19); "lower bound on the supremum" as: $\tau^*$ is below every upper bound of that set. The optimal solution of (20) is a hypothesis, as in the theorem. $\succeq 0$ in (20) is nonnegativity of the quadratic form, because the lower-right block of (20c) is not symmetric.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 21, Theorem 3.8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
import Definitions.Def_WiesemannRMDP_AffineSDP_Model
import Definitions.Def_WiesemannRMDP_AffineSDP_Programs

namespace WiesemannRMDP.AffineSDP

open FoundationsML.ReinforcementLearning Matrix

/-- Theorem 3.8 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 21). Fix `π ∈ Π` and let `(τ*, w*, W*, γ*, Γ*)` be an optimal
solution of the semidefinite program (20); set `ϑ*(ξ) := w* + W* ξ`.

(a) If `L = 1`, then (19) and (20) are equivalent: `τ*` is the supremum of (19) — it is the
greatest objective value of a feasible solution of (19) — and `ϑ*` is feasible and optimal in
(19) (its objective value `inf_{ξ∈Ξ} p₀ᵀϑ*(ξ)` equals `τ*`).

(b) If `L > 1`, then (20) is a conservative approximation of (19): `τ*` is a lower bound on
the supremum of (19) (it is below every upper bound of the objective values of (19)), `ϑ*` is
feasible in (19), and `inf_{ξ∈Ξ} p₀ᵀϑ*(ξ) = τ*`.

**Formalization Note.** The affine `ϑ : Ξ ↦a ℝ^S` of (19) are encoded as `ϑ(ξ) = w + W ξ`, as
in the paper's own reformulation (21). The optimal solution of (20) is a hypothesis, as in the
theorem ("Let … denote an optimal solution"). `⪰ 0` in (20) is `IsPSDForm`. -/
theorem theorem_3_8 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (γ : Fin L → ℝ) (Γ : St → Fin L → ℝ) (hopt : M.IsOpt20 π τ w W γ Γ) :
    (L = 1 →
        IsGreatest (M.values19 π) τ ∧ M.Feas19 π w W ∧ M.val19 w W = τ) ∧
      (1 < L →
        τ ∈ lowerBounds (upperBounds (M.values19 π)) ∧ M.Feas19 π w W ∧
          M.val19 w W = τ) := by sorry

end WiesemannRMDP.AffineSDP
