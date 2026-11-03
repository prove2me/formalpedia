-- Prove2me | Theorems.Thm_WeaklyCoupledDP_alp_le_lagrangian
-- name    : WeaklyCoupledDP.alp_le_lagrangian
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:18.829858+00:00
-- url     : https://prove2.me/theorems/49d6f685-dcb8-4b3a-ab02-c622232a0643
-- title:
--   §3.3 — the ALP bound is tighter, $V^{\mathrm{LP}}_1(s_1,e_1) \le V^\lambda_1(s_1,e_1)$ for every $\lambda \in \Lambda$
-- statement:
--   For every multiplier $\lambda \in \Lambda$ there is a feasible solution $V$ of the approximate linear program (5) with
--   $$
--   \sum_{i=1}^N V_{1,i}(s_{1,i},e_1) \le V^\lambda_1(s_1,e_1).
--   $$
--   Hence $V^{\mathrm{LP}}_1(s_1,e_1) \le V^\lambda_1(s_1,e_1)$ for every $\lambda \in \Lambda$, and $V^{\mathrm{LP}}_1(s_1,e_1) \le V^{\lambda*}_1(s_1,e_1)$: the ALP relaxation gives a tighter upper bound than the Lagrangian relaxation. The difference $V^{\lambda*}_1 - V^{\mathrm{LP}}_1 \ge 0$ is the **relaxation gap** studied in §4.
--
--   Differences from the source:
--   - generalization: V^LP₁(s₁,e₁) ≤ V^λ₁(s₁,e₁), with V^LP₁ the ALP optimum → some ALP-feasible V has objective at most V^λ₁(s₁,e₁); reason: it does not presuppose that the ALP optimum exists, and it implies the printed inequality.
--   - reading: (5b) uses V_{T+1,i} without a value → ALP feasibility includes V_{T+1,i} = 0; reason: the convention V_{T+1} = 0 of (2) and (7); without it the ALP is unbounded below.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §3.3, p.9 (PDF p.10); outer inequality of Proposition 3.3, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible
import Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue

namespace WeaklyCoupledDP

/-- **§3.3** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.9): `V^LP₁(s₁, e₁) ≤ V^λ₁(s₁, e₁)` for any
`λ ∈ Λ`, i.e., the ALP relaxation provides a tighter upper bound than the Lagrangian relaxation.

**Formalization Note.** Stated as: for every `λ ∈ Λ` there is an ALP-feasible `V` whose objective is
at most `V^λ₁(s₁, e₁)`. This does not presuppose that the ALP optimum exists. -/
theorem alp_le_lagrangian {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*}
    {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E]
    (M : Model N S E Act L) (lam : M.Multiplier) (hlam : lam ∈ M.Lambda) :
    ∃ V : M.ValueArray, M.ALPFeasible V ∧
      M.alpObjective V ≤ M.lagrangianValue lam 1 M.s₁ M.e₁ := by sorry

end WeaklyCoupledDP
