-- Prove2me | Theorems.Thm_QualityEncroach_Differ_proposition_4_ii
-- name    : QualityEncroach.Differ.proposition_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:25.365694+00:00
-- url     : https://prove2.me/theorems/6b73843c-313b-452a-a6af-ec1e391f236b
-- title:
--   Proposition 4(ii), p. 16 — under quality differentiation, when encroachment happens Π*_M > 1/(54k) and Π*_R < 1/(108k)
-- statement:
--   Consider the encroachment game with quality differentiation of §5. A manufacturer chooses a wholesale price $w$, a quality $u>0$ for the product she sells directly and a quality $tu$, $t>0$, for the product she sells through a retailer. The retailer then orders $q_R\ge0$, and finally the manufacturer sells $q_M\ge0$ directly. Consumer types are uniform on $[0,1]$; producing one unit of quality $v$ costs $kv^2$ with $k>0$, and each unit sold directly costs a further $c\ge0$.
--
--   In every subgame-perfect equilibrium in which the manufacturer encroaches, i.e. sells $q^*_M>0$ directly on the equilibrium path, the equilibrium profits satisfy
--
--   $$
--   \Pi^*_M>\Pi^N_M=\frac{1}{54k}
--   \qquad\text{and}\qquad
--   \Pi^*_R<\Pi^N_R=\frac{1}{108k},
--   $$
--
--   where $\Pi^N_M$ and $\Pi^N_R$ are the equilibrium profits of the benchmark without a direct channel (§3.2). When encroachment happens, the manufacturer always wins and the retailer always loses, even though the manufacturer may offer the retailer a differentiated product.
--
--   **Formalization Note.** The benchmark profits are written as the constants $\frac1{54k}$ and $\frac1{108k}$; the milestone *benchmark equilibrium* shows that these are the equilibrium profits of the benchmark game.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 16, Proposition 4(ii) (proof: p. 32); benchmark profits p. 9

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem proposition_4_ii (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by sorry

end QualityEncroach.Differ
