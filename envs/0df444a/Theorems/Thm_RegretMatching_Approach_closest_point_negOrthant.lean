-- Prove2me | Theorems.Thm_RegretMatching_Approach_closest_point_negOrthant
-- name    : RegretMatching.Approach.closest_point_negOrthant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:00.501186+00:00
-- url     : https://prove2.me/theorems/1ab40ab0-3dcf-4515-8b12-4c352196f548
-- title:
--   §3, proof of THEOREM A, p. 1137 — D_t has coordinates Dⁱ_t(j,k), F(D_t) = [D_t]⁻ and λ(D_t) = [D_t]⁺ = (Rⁱ_t(j,k))
-- statement:
--   Fix a player $i$, let $L=\{(j,k)\in S^i\times S^i: j\ne k\}$, and let $v$ be the vector payoff of the proof of Theorem A. Then:
--   1. for every history $h_t$ with $t\ge1$, the average vector payoff $D_t=\frac1t\sum_{\tau\le t}v(s_\tau)$ has $(j,k)$-coordinate $D^i_t(j,k)$;
--   2. for every $x\in\mathbb R^L$, the point $[x]^-$ (coordinatewise $\min\{x,0\}$) lies in $\mathbb R^L_-$, is a closest point of $\mathbb R^L_-$ to $x$ in Euclidean distance, and is the only one;
--   3. for every $x\in\mathbb R^L$, $x-[x]^-=[x]^+$;
--   4. for every history $h_t$ with $t\ge1$, $[D_t]^+$ has $(j,k)$-coordinate $R^i_t(j,k)$.
--
--   Hence $F(D_t)=[D_t]^-$ and $\lambda(D_t)=D_t-F(D_t)=[D_t]^+=(R^i_t(j,k))_{(j,k)\in L}$ is the vector of regrets at time $t$, so that a strategy satisfying (3.1) at time $t+1$ is exactly a Blackwell procedure for $\mathbb R^L_-$.
--
--   **Formalization Note.** The page states the closest-point claim for $D_t\notin\mathbb R^L_-$; it is stated here for every $x$ (for $x\in\mathbb R^L_-$ it says $[x]^-=x$). Histories have length $t+1\ge1$ in Lean.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1137, proof of THEOREM A, Figure 2

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem closest_point_negOrthant
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι) :
    (∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)) (l : OffDiag (S i)),
        avgPay u i h l = RegretMatching.Main.regretD u h i l.1.1 l.1.2) ∧
      (∀ x : EuclideanSpace ℝ (OffDiag (S i)),
        negPart x ∈ negOrthant (OffDiag (S i)) ∧
          (∀ c ∈ negOrthant (OffDiag (S i)), dist x (negPart x) ≤ dist x c) ∧
          (∀ c ∈ negOrthant (OffDiag (S i)), dist x c ≤ dist x (negPart x) → c = negPart x)) ∧
      (∀ x : EuclideanSpace ℝ (OffDiag (S i)), x - negPart x = posPart x) ∧
      (∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)) (l : OffDiag (S i)),
        posPart (avgPay u i h) l = RegretMatching.Main.regretR u h i l.1.1 l.1.2) := by sorry

end RegretMatching.Approach
