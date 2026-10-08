-- Prove2me | Theorems.Thm_PriceOfStability_Undirected_deviation_inequality
-- name    : PriceOfStability.Undirected.deviation_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:23.029428+00:00
-- url     : https://prove2.me/theorems/4f9e7f35-0e73-4845-be7c-291abde693f8
-- title:
--   Claim 4.1, proof — the deviation inequalities $x_1+x_2+y_2/2+y_3/2\ge y_1+y_3/2$ and its mirror
-- statement:
--   Consider the two-player undirected fair connection game with nonnegative edge costs, common terminal $s$ and personal terminals $t_1,t_2$. Let $(S_1',S_2')$ be a pure Nash equilibrium and let $(S_1,S_2)$ be a profile in which each $S_i$ is an inclusion-minimal set of edges connecting $t_i$ with $s$. With $x_1=\mathrm{cost}(S_1\setminus S_2)$, $x_2=\mathrm{cost}(S_2\setminus S_1)$, $y_1=\mathrm{cost}(S_1'\setminus S_2')$, $y_2=\mathrm{cost}(S_2'\setminus S_1')$, $y_3=\mathrm{cost}(S_1'\cap S_2')$,
--   $$y_1+\tfrac{y_3}{2}\ \le\ x_1+x_2+\tfrac{y_2}{2}+\tfrac{y_3}{2}\qquad\text{and}\qquad y_2+\tfrac{y_3}{2}\ \le\ x_1+x_2+\tfrac{y_1}{2}+\tfrac{y_3}{2}.$$
--
--   The left sides are the players' payments at the equilibrium; the right sides bound what player 1 (resp. 2) would pay by deviating to $X_1\cup X_2\cup Y_2\cup Y_3$ (resp. $X_1\cup X_2\cup Y_1\cup Y_3$), which still connects its terminals.
--
--   **Formalization Note.** Inclusion-minimality of $S_1,S_2$ is implicit in the paper, which treats them as paths. It is needed: if $S_1=S_2$ is a non-minimal common tree, then $x_1=x_2=0$ and the inequalities can fail. The optimal solution of Claim 4.1 can always be pruned to minimal strategies without increasing its cost. Players $1,2$ are `0`, `1`.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Claim 4.1, proof (deviation of player 1 and symmetric reasoning)

import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- The deviation inequalities (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof,
p. 1613, PDF p. 12). Let `(S′₁, S′₂)` be a Nash equilibrium of the two-player undirected fair
connection game with nonnegative edge costs and `(S₁, S₂)` a profile in which each `Sᵢ` is an
inclusion-minimal strategy. With `xᵢ`, `yᵢ` as in (4.1), player 1's deviation to
`X₁ ∪ X₂ ∪ Y₂ ∪ Y₃` and player 2's symmetric deviation give
`x₁ + x₂ + y₂/2 + y₃/2 ≥ y₁ + y₃/2` and `x₁ + x₂ + y₁/2 + y₃/2 ≥ y₂ + y₃/2`.

**Formalization Note.** The inclusion-minimality of `S₁`, `S₂` is implicit in the paper, whose
argument ("following X₁ until X₁ meets with X₂, then following X₂ back to t₂") treats them as paths;
for arbitrary connecting sets `X₁ ∪ X₂` need not connect `t₁` with `t₂`. Players `0`, `1` are the
paper's 1, 2. -/
theorem deviation_inequality {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 1 \ S' 0) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 ∧
      setCost c (S' 1 \ S' 0) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 0 \ S' 1) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 := by sorry

end PriceOfStability.Undirected
