-- Prove2me | Theorems.Thm_SDDiP_Conv_eq_3_8
-- name    : SDDiP.Conv.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:40.719246+00:00
-- url     : https://prove2.me/theorems/a29cfb99-e282-4967-84c5-aa59bbdb7a3c
-- title:
--   (3.8a)–(3.8f) — a sampled node whose children are exact becomes exact after its backward step
-- statement:
--   Consider a run of the SND algorithm with valid and tight cuts, lower bounds $L_n\le\mathcal Q_n$ and a solver returning optimal nodal solutions. Suppose that at iteration $i$ the node $n$, which is not in the last stage, is sampled ($n\in\Omega^i$), and that every child is exact at its forward solution:
--   $$\psi^i_m(x^i_m) = \mathcal Q_m(x^i_m)\qquad\forall m\in\mathcal C(n).$$
--   Then after the backward step of iteration $i$ the approximation of $n$ is exact at the forward state $x^i_n$:
--   $$\psi^{i+1}_n(x^i_n) = \mathcal Q_n(x^i_n).$$
--
--   This is the chain (3.8a)–(3.8f) in the proof of Claim 2, which shows that each block of iterations without change is followed by a change once the offending node is sampled again.
--
--   **Formalization Note** The printed chain has index slips: (3.8b) writes $\psi^{j_k}_m$ where tightness (3.5) refers to the updated $\psi^{j_k+1}_m$ (as the sentence after the display says), (3.8c)'s equality is an inequality when the child's approximation grew in the same backward step, (3.8d) writes $\mathcal Q^{j_k}_m$ for $\mathcal Q_m$, and (3.8e) writes $Q^{j_k}_m(x, \psi^{j'_k}_m)$ for the true value $Q_m(x^{j_k}_{n_{j_k}})$. The statement is the intended one, at a single iteration $i$ (in the proof, iteration $j'_k$ has the same forward solution and approximations as $j_k$, by (A3)).
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 476, proof of Claim 2, (3.8a)–(3.8f)

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage

/-- (3.8a)–(3.8f), proof of Claim 2, p. 476 (Zou–Ahmed–Sun 2019): in a run with valid and tight cuts,
if at iteration `i` a node `n` that is not in the last stage is sampled and every child `m ∈ C(n)` is
exact at its forward solution, `ψ^i_m(x^i_m) = 𝒬_m(x^i_m)`, then after the backward step of iteration
`i` the approximation of `n` is exact at the forward state: `ψ^{i+1}_n(x^i_n) = 𝒬_n(x^i_n)`. -/
theorem eq_3_8 {H d ℓ M : ℕ} (D : Model H d ℓ) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d)
    (hvalid : D.ValidCuts s κ) (htight : D.TightCuts L sol s κ)
    (i : ℕ) (n : D.T.Node) (hn : D.Sampled (s i) n) (hnl : ¬ D.IsLeaf n)
    (hchild : ∀ m ∈ D.T.children n, D.approx L s κ i m (D.forwardSol L sol s κ i m).1 =
      D.Qcal m (D.forwardSol L sol s κ i m).1) :
    D.approx L s κ (i + 1) n (D.forwardSol L sol s κ i n).1 =
      D.Qcal n (D.forwardSol L sol s κ i n).1 := by sorry

end SDDiP.Conv
