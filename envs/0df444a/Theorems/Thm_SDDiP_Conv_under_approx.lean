-- Prove2me | Theorems.Thm_SDDiP_Conv_under_approx
-- name    : SDDiP.Conv.under_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:47:49.519064+00:00
-- url     : https://prove2.me/theorems/0409db49-89ad-47e2-837e-f0acee59da24
-- title:
--   Proof of Claim 1 — valid cuts give under-approximations: $\psi^i_n\le\mathcal Q_n$ and $\underline Q^i_n\le Q_n$
-- statement:
--   Consider a run of the SND algorithm on the model of the mission, with lower bounds satisfying $L_n \le \mathcal Q_n(x)$ for every node $n$ before the last stage and every $x\in\{0,1\}^d$, and with valid cuts (3.4). Then for every iteration $i$ and every node $n$ the approximation is an under-approximation of the expected cost-to-go function,
--   $$\psi^i_n(x) \le \mathcal Q_n(x)\qquad\forall x\in\{0,1\}^d,$$
--   and consequently the approximate nodal value is a lower bound on the true value function:
--   $$\underline Q^i_n(\hat x, \psi^i_n) \le Q_n(\hat x)\qquad\forall \hat x\in\{0,1\}^d.$$
--
--   This is the first step of the proof of Claim 1 and the reason the forward problem at the root yields a lower bound.
--
--   **Formalization Note** The hypothesis on $L_n$ is the "initial under-approximation" of Algorithm 1, line 1, since $\psi^1_n = L_n$ by (3.2). At the scenarios $\psi^i_n\equiv 0 = \mathcal Q_n$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 475, proof of Claim 1 (first two sentences)

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage

/-- Proof of Claim 1, p. 475 (Zou–Ahmed–Sun 2019): along a run of the SND algorithm whose cuts are
valid and whose lower bounds `L_n` under-estimate `𝒬_n`, every approximation `ψ^i_n` is an
under-approximation of the expected cost-to-go function `𝒬_n` on `{0,1}^d`, and therefore
`Q̲^i_n(x_{a(n)}, ψ^i_n) ≤ Q_n(x_{a(n)})` for every binary parent state. -/
theorem under_approx {H d ℓ M : ℕ} (D : Model H d ℓ) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hvalid : D.ValidCuts s κ)
    (i : ℕ) (n : D.T.Node) :
    (∀ x, D.approx L s κ i n x ≤ D.Qcal n x) ∧
      ∀ xa : Fin d → Bool, D.nodalValue n (toReal xa) (D.approx L s κ i n) ≤ D.Q n xa := by sorry

end SDDiP.Conv
