-- Prove2me | Theorems.Thm_QualityEncroach_Differ_proposition_1_iii
-- name    : QualityEncroach.Differ.proposition_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:18.668682+00:00
-- url     : https://prove2.me/theorems/521413dd-0601-45a2-8883-7f383c8267db
-- title:
--   Proposition 1(iii), p. 11 — with uniform quality, when encroachment happens Π^U_M > 1/(54k) and Π^U_R < 1/(108k)
-- statement:
--   Consider the encroachment game with uniform quality (§4.1): the manufacturer chooses a wholesale price $w$ and a quality $u>0$, the same in both channels; the retailer orders $q_R\ge0$; the manufacturer then sells $q_M\ge0$ directly; both face the price $u(1-q_M-q_R)$. Let $k>0$ and $c\ge0$.
--
--   In every subgame-perfect equilibrium in which the manufacturer encroaches ($q_M>0$ on the path), the equilibrium profits satisfy
--
--   $$
--   \Pi^U_M>\Pi^N_M=\frac{1}{54k}
--   \qquad\text{and}\qquad
--   \Pi^U_R<\Pi^N_R=\frac{1}{108k},
--   $$
--
--   where $\Pi^N_M$, $\Pi^N_R$ are the benchmark equilibrium profits without a direct channel (§3.2). The manufacturer wins and the retailer loses.
--
--   The proof of Proposition 4(ii) uses this result for the costs at which the manufacturer encroaches without differentiating.
--
--   **Formalization Note.** The uniform-quality game is the game of this mission with the ratio fixed at $t=1$. The benchmark profits enter as the constants $\frac1{54k}$, $\frac1{108k}$, which the milestone *benchmark equilibrium* derives from the benchmark game.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 11, Proposition 1(iii) (proof: p. 29); benchmark profits p. 9

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem proposition_1_iii (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c {1} σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by sorry

end QualityEncroach.Differ
