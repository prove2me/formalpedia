-- Prove2me | Theorems.Thm_ResetInventory_proposition_2_expected_cost_to_go
-- name    : ResetInventory.proposition_2_expected_cost_to_go
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:35.962303+00:00
-- url     : https://prove2.me/theorems/68906f13-40f1-4644-96f8-9eb586905505
-- title:
--   Proposition 2 — smoothness of the expected cost-to-go
-- statement:
--   **Proposition 2.** Let the demand density $f$ satisfy Assumption 5 with constants $L,P$, let $c_{\max}\ge0$, and let $V=J(\cdot,t+1)$ be continuous and piecewise $C^1$ on $[0,c_{\max}]$ with derivative bounded by $M=M_{t+1}$ (Assumption T, without its Lipschitz requirement). Then $z\mapsto\mathbb E\,V((z-w)^+)$ has a derivative $D$ on $[0,c_{\max}]$ that is Lipschitz with the non-negative constant $(Lc_{\max}+P)M_{t+1}$ and absolutely bounded by $M_{t+1}$:
--   $$
--   |D(z)|\le M_{t+1},\qquad |D(z)-D(z')|\le(Lc_{\max}+P)\,M_{t+1}\,|z-z'|\qquad(z,z'\in[0,c_{\max}]).
--   $$
--   Taking the expectation over the demand smooths the cost-to-go. A piecewise $C^1$ function with kinks becomes a function with a Lipschitz derivative, which is what lets a strongly convex stage cost absorb it in Proposition 3.
--
--   Differences from the source:
--   - generalization: if A1–A5 and AT hold → only A5 and c_max ≥ 0 are assumed, besides the condition on V; reason: the statement concerns only the demand density and J(·,t+1); A1 is built into the expectation, and A2–A4 are not used
--   - generalization: AT: J(·,t+1) is piecewise differentiable on a partition of [0, c_max], each piece's derivative bounded by M_{t+1} and Lipschitz continuous → PiecewiseC1: continuous, piecewise C¹ on a partition of [0, c_max] with derivative bounded by M_{t+1}, no Lipschitz requirement on the derivatives; reason: the proofs use only the continuity of the pieces and their derivatives and the bound M_{t+1}; every function satisfying AT satisfies PiecewiseC1
--   - generalization: the value function J(·,t+1) → any function V satisfying PiecewiseC1; reason: the proposition uses only the stated properties of J(·,t+1); the paper's J(·,t+1) is an instance
--   - reading: states x ∈ ℝ₊ (A1), with AT on the domain [0, c_max] → every state, equation and conclusion on x ∈ [0, c_max]; reason: AT and the proofs of Propositions 5 and 6 work on [0, c_max]; from x ≤ c_max the dynamics stay in [0, c_max], and for x > c_max the order set U = [0, c_max − x] of A4 is empty
--   - encoding: derivatives ∂ₓH, ∂ₓₓH, ∂ₓR, ∂_zJ_i and the derivatives in the conclusions → derivatives within [0, c_max] (one-sided at 0 and c_max), with the derivative functions named explicitly; reason: at interior points this is the ordinary derivative; at the ends the paper's functions live on [0, c_max], and its retail example (∂ₓₓH = (p+q)f with a jump of f at 0) needs one-sided derivatives
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 2, p.17; proof, pp.30–31

import Mathlib
import Definitions.Def_ResetInventory_A5
import Definitions.Def_ResetInventory_expectedNext
import Definitions.Def_ResetInventory_PiecewiseC1

namespace ResetInventory

/-- **Proposition 2** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.17. If A1–A5 and AT
hold, then `E(J((z − w)⁺, t + 1))` has a derivative that is Lipschitz continuous with
non-negative constant `(L c_max + P) M_{t+1}`, and the derivative is absolutely bounded by
`M_{t+1}`.

Here `V = J(·, t + 1)` and `M = M_{t+1}`; the conclusion is on `z ∈ [0, c_max]`.

**Formalization Note** AT is `PiecewiseC1` (continuous, piecewise `C¹` with derivative bounded by
`M` on a finite partition of `[0, c_max]`), without AT's requirement that the derivative of each
piece be Lipschitz; the proof (pp.30–31) uses only the continuity of the pieces and their
derivatives and the bound `M`. Only A5 and `c_max ≥ 0` are assumed (A1 is built into
`expectedNext`; A2–A4 are not used). The derivative is within `[0, c_max]`, one-sided at `0` and
`c_max`, and named explicitly (`D`). -/
theorem proposition_2_expected_cost_to_go (cmax L P M : ℝ) (f V : ℝ → ℝ)
    (hcmax : 0 ≤ cmax) (hf : A5 f L P) (hV : PiecewiseC1 cmax M V) :
    ∃ D : ℝ → ℝ,
      (∀ z ∈ Set.Icc 0 cmax, HasDerivWithinAt (expectedNext f V) (D z) (Set.Icc 0 cmax) z) ∧
      (∀ z ∈ Set.Icc 0 cmax, |D z| ≤ M) ∧
      (∀ z ∈ Set.Icc 0 cmax, ∀ z' ∈ Set.Icc 0 cmax,
        |D z - D z'| ≤ (L * cmax + P) * M * |z - z'|) := by sorry

end ResetInventory
