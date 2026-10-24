-- Prove2me | Theorems.Thm_PoWMining_CostStatics_proposition_4_6
-- name    : PoWMining.CostStatics.proposition_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:53.277981+00:00
-- url     : https://prove2.me/theorems/ecb84368-347d-4f8b-aaa7-72b52687f293
-- title:
--   Proposition 4.6, p. 17 — signs of the cost sensitivities of equilibrium hash rates and shares; the indirect one is positive iff the share is below 1/2
-- statement:
--   Consider $n \ge 2$ miners, all active in the equilibrium of the proof-of-work mining game, with costs-per-hash $c_k > 0$, capacity parameter $\gamma \ge 0$ and reward $R > 0$. Let $H^* = g$ be the aggregate equilibrium hash rate (4.1), $h^*_i = f_i(g) = g(R - c_i g)/(R + \gamma g^2)$ the equilibrium hash rate of miner $i$ (B.3), and let
--   $$\Delta_{i,1} = \frac{\partial f_i}{\partial c_i},\quad \Delta_{i,2} = \frac{\partial f_i}{\partial g}\frac{\partial g}{\partial c_i},\quad \widetilde\Delta_{i,1} = \frac1g\frac{\partial f_i}{\partial c_i},\quad \widetilde\Delta_{i,2} = \frac1g\frac{\partial g}{\partial c_i}\Big(\frac{\partial f_i}{\partial g} - \frac{f_i}{g}\Big)$$
--   be the direct and indirect sensitivities (the first two as in (B.4), the last two from the decomposition on p. 42). For active miners $i \ne j$:
--
--   1. $h^*_i$ is differentiable in $c_i$ and in $c_j$, with
--   $$\frac{\partial h^*_i}{\partial c_i} = \Delta_{i,1} + \Delta_{i,2} < 0,\qquad \frac{\partial h^*_i}{\partial c_j} = \Delta_{i,2};$$
--   2. $\Delta_{i,1} < 0$, and
--   $$\Delta_{i,2} > 0 \iff \frac{h^*_i}{H^*} < \frac12; \tag{4.5}$$
--   3. the share $h^*_i/H^*$ is differentiable in $c_i$ and in $c_j$, with
--   $$\frac{\partial}{\partial c_i}\frac{h^*_i}{H^*} = \widetilde\Delta_{i,1} + \widetilde\Delta_{i,2} < 0,\qquad \frac{\partial}{\partial c_j}\frac{h^*_i}{H^*} = \widetilde\Delta_{i,2} > 0,$$
--   where $\widetilde\Delta_{i,1} < 0$ and $\widetilde\Delta_{i,2} > 0$.
--
--   A higher own cost always lowers a miner's hash rate and share. The indirect channel through the aggregate cushions this for small miners (share below one half) and amplifies it for a dominant one, and it is exactly the response of $h^*_i$ to a competitor's cost.
--
--   **Formalization Note.** The paper's "sensitivities" are derivatives at a state where small parameter changes do not alter the set of active miners (pp. 15–16); they are taken here of the closed forms (B.3) of the $n$ active miners, as in the paper's proof, under the hypothesis that all $n$ are active ($R - c_k g > 0$). The four $\Delta$'s are defined by derivatives, not by their closed forms. The paper never defines $\widetilde\Delta_{i,1}, \widetilde\Delta_{i,2}$; the reading above is pinned by its p. 42 decomposition. Derivatives are one-variable derivatives along `Function.update`, stated with `HasDerivAt`. $\gamma = 0$ is allowed. Miner indices are 0-based (`Fin n`).
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 17, Proposition 4.6 (proof pp. 39–42)

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem proposition_4_6 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => hstar (Function.update c i t) γ R i)
      (Delta1 c γ R i + Delta2 c γ R i) (c i) ∧
    Delta1 c γ R i + Delta2 c γ R i < 0 ∧
    HasDerivAt (fun t => hstar (Function.update c j t) γ R i) (Delta2 c γ R i) (c j) ∧
    Delta1 c γ R i < 0 ∧
    (0 < Delta2 c γ R i ↔ share c γ R i < 1 / 2) ∧
    HasDerivAt (fun t => share (Function.update c i t) γ R i)
      (DeltaT1 c γ R i + DeltaT2 c γ R i) (c i) ∧
    DeltaT1 c γ R i + DeltaT2 c γ R i < 0 ∧
    HasDerivAt (fun t => share (Function.update c j t) γ R i) (DeltaT2 c γ R i) (c j) ∧
    0 < DeltaT2 c γ R i ∧
    DeltaT1 c γ R i < 0 := by sorry

end PoWMining.CostStatics
