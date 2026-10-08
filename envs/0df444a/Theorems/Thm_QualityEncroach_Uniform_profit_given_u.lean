-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_profit_given_u
-- name    : QualityEncroach.Uniform.profit_given_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:20.341591+00:00
-- url     : https://prove2.me/theorems/ad2c2c20-88f5-4841-9825-ebcc878e390a
-- title:
--   Proof of Proposition 1(i), p. 27 — the manufacturer's optimal profit given u is the three-case function Π_M(u)
-- statement:
--   Let $k>0$ and $c\ge0$, and let $\sigma$ be a strategy profile of the encroachment game with uniform quality whose retailer rule and stage-3 manufacturer rule are optimal at every node (the stage-2 and stage-3 conditions of subgame perfection). Then for every quality $u$ with $0<u<1/k$, the greatest profit the manufacturer can obtain by choosing a wholesale price $w$, with play continuing according to $\sigma$, is
--   $$\Pi_M(u)=\begin{cases}\Pi^U_M(u)=\dfrac{k^2u^3}{4}+\dfrac{kcu}{2}+\dfrac{7c^2}{12u}-\dfrac{ku^2}{2}+\dfrac u4-\dfrac c2 & \text{if } c\le \dfrac{3u(1-ku)}{5},\\[2mm] \Pi^{UZ}_M(u)=\big(\tfrac12ku^2-\tfrac12u+\tfrac32c\big)\big(1-\tfrac cu-ku\big) & \text{if } \dfrac{3u(1-ku)}{5}\le c\le\dfrac{5u(1-ku)}{6},\\[2mm] \Pi^N_M(u)=\dfrac{u(1-ku)^2}{8} & \text{if } c\ge \dfrac{5u(1-ku)}{6},\end{cases}$$
--   and this maximum is attained.
--
--   The three cases correspond to the manufacturer selling directly, the retailer ordering exactly enough to deter direct sales, and the direct channel being irrelevant. This is the reduced problem in $u$ on which the proofs of Proposition 1 operate.
--
--   **Formalization Note.** The statement is "$\Pi_M(u)$ is the greatest element of the set of profits $\{\Pi_M(w,u): w\in\mathbb R\}$". The bound $u<1/k$ is the paper's footnote 1 (p. 28). At the two case boundaries the adjacent formulas agree, so the Lean `if` chooses the first applicable case.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 26–27, Appendix, proof of Proposition 1(i), display at the top of p. 27; footnote 1, p. 28

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- Proof of Proposition 1(i), p. 27: if the retailer's and the manufacturer's quantity rules of
`σ` are optimal at every node (stages 2 and 3 of subgame perfection), then for every quality
`0 < u < 1/k` the manufacturer's greatest profit over wholesale prices `w` is the three-case
function `Π_M(u)`. -/
theorem profit_given_u (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (h3 : Stage3Optimal k c σ) (h2 : Stage2Optimal σ) (u : ℝ) (hu : 0 < u) (huk : u < 1 / k) :
    IsGreatest (Set.range fun w : ℝ => mfrPayoff k c (σ.outcomeAtOrder w u)) (PiM k c u) := by sorry

end QualityEncroach.Uniform
