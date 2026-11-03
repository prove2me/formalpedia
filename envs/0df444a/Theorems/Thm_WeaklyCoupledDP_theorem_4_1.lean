-- Prove2me | Theorems.Thm_WeaklyCoupledDP_theorem_4_1
-- name    : WeaklyCoupledDP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:34.020233+00:00
-- url     : https://prove2.me/theorems/dcd894f8-b0ac-4464-a076-a3d3093a40f9
-- title:
--   Theorem 4.1 — the relaxation gap is at most the expected integrality gap of the separation problems
-- statement:
--   For every feasible solution $V$ of the approximate linear program (5) there is a multiplier $\lambda \in \Lambda$ with
--   $$
--   V^\lambda_1(s_1,e_1) - \sum_{i=1}^N V_{1,i}(s_{1,i},e_1) \le \sum_{t=1}^T \mathbb E_{e_t}\big[\Delta^V_t(e_t,\ell_t,b_t)\big],
--   $$
--   where $\Delta^V_t(e_t,\ell_t,b_t)$ is the integrality gap between the $(t,e_t)$-separation problem (6) for $V$ and its LP relaxation (9), and $\mathbb E_{e_t}$ is the expectation over $e_t$ given $e_1$. Applied to an optimal solution $V^{\mathrm{LP}}$ of the ALP, and since $V^{\lambda*}_1 \le V^\lambda_1$, this is the paper's statement
--   $$
--   V^{\lambda*}_1(s_1,e_1) - V^{\mathrm{LP}}_1(s_1,e_1) \le \sum_{t=1}^T \mathbb E_{e_t}\big[\Delta^{V^{\mathrm{LP}}}_t(e_t,\ell_t,b_t)\big].
--   $$
--   The bound holds for every weakly coupled DP; it reduces questions about the relaxation gap to integrality gaps of one-period integer programs.
--
--   Differences from the source:
--   - generalization: for an optimal ALP solution V^LP, a bound on V^λ*₁ − V^LP₁ → for every ALP-feasible V, some λ ∈ Λ with V^λ₁ − Σᵢ V₁,ᵢ bounded by the same sum; reason: the proof uses only feasibility of V, and for an optimal V it gives the printed bound because V^λ*₁ ≤ V^λ₁.
--   - encoding: Δ^V_t as the difference of two minima → the difference of two infima (sInf); reason: for 1 ≤ t ≤ T both feasible sets are nonempty and compact, so both infima are attained minima and the values agree.
--   - encoding: E_{eₜ}[·] → the expectation of eₜ given e₁ computed through Q₁,…,Q_{t−1}; reason: the paper's E_{eₜ} is the expectation over eₜ from the given initial state.
--   - reading: (5b) uses V_{T+1,i} without a value → ALP feasibility includes V_{T+1,i} = 0; reason: the convention V_{T+1} = 0 of (2) and (7); without it the ALP is unbounded below.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), Theorem 4.1, p.12 (PDF p.13); proof, pp.24–26 (PDF pp.25–27)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue
import Definitions.Def_WeaklyCoupledDP_Model_integralityGap

open Finset

namespace WeaklyCoupledDP

/-- **Theorem 4.1** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.12). For any optimal solution
`V^LP` of the ALP relaxation (5), the relaxation gap satisfies
`V^λ*₁(s₁, e₁) − V^LP₁(s₁, e₁) ≤ ∑_{t=1}^T E_{eₜ}[Δ^{V^LP}_t(eₜ, ℓₜ, bₜ)]`.

**Formalization Note.** Stated for every ALP-feasible `V`, and with a witness `λ ∈ Λ`: the proof uses
only feasibility of `V`. For an optimal `V`, since `V^λ*₁(s₁, e₁) ≤ V^λ₁(s₁, e₁)`, this gives the
printed inequality. `E_{eₜ}` is the expectation of `eₜ` given `e₁` (`M.exoProb`). -/
theorem theorem_4_1 {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*}
    {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)
    (V : M.ValueArray) (hV : M.ALPFeasible V) :
    ∃ lam ∈ M.Lambda, M.lagrangianValue lam 1 M.s₁ M.e₁ - M.alpObjective V ≤
      ∑ t ∈ Icc 1 M.T, ∑ e, M.exoProb t e * M.integralityGap V t e := by sorry

end WeaklyCoupledDP
