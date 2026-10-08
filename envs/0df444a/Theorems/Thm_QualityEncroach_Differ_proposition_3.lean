-- Prove2me | Theorems.Thm_QualityEncroach_Differ_proposition_3
-- name    : QualityEncroach.Differ.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:32.612793+00:00
-- url     : https://prove2.me/theorems/a2a94955-ad8e-468a-ab43-863dc5f02dfa
-- title:
--   Proposition 3, p. 15 — under encroachment the manufacturer never sells strictly lower quality directly (t* ≤ 1)
-- statement:
--   Consider the encroachment game with quality differentiation (§5): the manufacturer chooses a wholesale price $w$, a direct quality $u>0$ and a retailer quality $tu$ with $t>0$; the retailer orders $q_R\ge0$; the manufacturer then sells $q_M\ge0$ directly. Let $k>0$ and $c\ge0$.
--
--   In every subgame-perfect equilibrium in which the manufacturer encroaches (sells $q_M>0$ directly on the equilibrium path), her choice of ratio satisfies
--
--   $$
--   t^*\le 1 ,
--   $$
--
--   that is, the product she sells directly has quality $u^*\ge t^*u^*$: she never offers a product of strictly lower quality through the direct channel.
--
--   This is the paper's answer to which channel should carry the higher quality: the direct one.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 15, Proposition 3 (proof: p. 30)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem proposition_3 (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) :
    σ.t ≤ 1 := by sorry

end QualityEncroach.Differ
