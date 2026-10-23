-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_scaling_step
-- name    : RepeatedNRM.Myopic.scaling_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:14.408274+00:00
-- url     : https://prove2.me/theorems/109a6312-6ba4-4911-a3ef-b9c4928e89d6
-- title:
--   Proof of Theorem 1, p. ec10 — (1 − γ)X(φ^{t−1}(b₁,1)) ⊆ X(φ^{t−1}(b₁,1−γ)), hence J^LBMY ≥ (1 − γ)J^relax
-- statement:
--   Let $\gamma\in[0,1]$, let every $\varphi_j$ satisfy Assumption 1(iii), and let $\mathbf b_1\in[0,1]^m$. For every period $t\in\{1,\dots,T\}$, scaling a feasible allocation of the optimistic budgets by $1-\gamma$ gives a feasible allocation of the pessimistic ones:
--   $$(1-\gamma)\,X\bigl(\boldsymbol\varphi^{t-1}(\mathbf b_1,\mathbf 1)\bigr)\subseteq X\bigl(\boldsymbol\varphi^{t-1}(\mathbf b_1,\mathbf 1-\boldsymbol\gamma)\bigr).$$
--   Consequently the value of (EC.6) dominates $1-\gamma$ times the value of the relaxation (9):
--   $$J^{LBMY}_T(\mathbf b_1)\ \ge\ (1-\gamma)\,J^{\mathrm{relax}}_T(\mathbf b_1),$$
--   where $J^{LBMY}_T(\mathbf b_1)=\sum_{t=1}^T\mathrm{MY}(\boldsymbol\varphi^{t-1}(\mathbf b_1,1-\gamma))$.
--
--   This is the second inequality in the printed proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: the step sits inside the proof of Theorem 1, under Assumptions 1 and 2 → only Assumption 1(iii) and $\gamma\in[0,1]$ are hypotheses; reason: the page derives the step from Assumption 1(iii) alone; the Lean statement specialises to the setting of Theorem 1
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - encoding: periods $t=1,\dots,T$ and $\varphi^{t-1}$ → `Finset.range T` with index $t$ for period $t+1$, and $\varphi^t$ with $\varphi^0 = \mathrm{id}$; reason: re-indexing only
--   - encoding: $J^{LBMY}_T$ and $J^{\mathrm{relax}}_T$ as maxima of the multi-period LPs (EC.6) and (9) → sums over periods of the one-period values $\mathrm{MY}$; reason: the paper's own identities (p. 17 and p. ec8): the constraints decouple across periods
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec10, proof of Theorem 1 (second inequality); (EC.6) p. ec7

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem scaling_step (I : Instance) (hI : I.Standing) (h1 : ∀ j, Assumption1iii I j)
    (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) :
    (∀ t ∈ Finset.range T, ∀ x : Fin I.n → Fin I.m → ℝ, feasible I (phiIterVec I t b1 1) x →
        feasible I (phiIterVec I t b1 (1 - γ)) ((1 - γ) • x)) ∧
      (1 - γ) * Jrelax I T b1 ≤ JLBMY I T b1 γ := by sorry
end RepeatedNRM.Myopic
