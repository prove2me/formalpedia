-- Prove2me | Theorems.Thm_QualityEncroach_NoCommit_stage3_no_uniform
-- name    : QualityEncroach.NoCommit.stage3_no_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:31.460179+00:00
-- url     : https://prove2.me/theorems/566e9863-c742-446a-90f8-5bc72beadcb2
-- title:
--   Proof of Proposition 7, p. 37 — at stage 3 with q_R > 0, an optimal (u_M, q_M) never has u_M = u_R and q_M > 0
-- statement:
--   Fix $k>0$, $c\ge0$, a wholesale price $w$, a retailer quality $u_R>0$ and a retailer order $q_R>0$. Suppose $(u_M,q_M)$ with $u_M>0$, $q_M\ge0$ maximizes the manufacturer's stage-3 profit
--   $$
--   \Pi_M(u_M',q_M') = (w-ku_R^2)q_R + (p_M - c - k u_M'^2)\,q_M'
--   $$
--   over all $u_M'>0$, $q_M'\ge0$, where $p_M$ is the direct-channel market-clearing price of the two-quality model. Then it is impossible that both $u_M=u_R$ and $q_M>0$:
--   $$
--   \neg\,(u_M = u_R \ \wedge\ q_M>0).
--   $$
--
--   In words: once the retailer has placed a positive order, the manufacturer never sells directly a product of the same quality as the retailer's. This is the contradiction that concludes the proof of Proposition 7, stated at every stage-3 history rather than only on the equilibrium path.
--
--   **Formalization Note.** The hypothesis $q_R>0$ is needed: the paper's contradiction $u_R(q_R+3ku_R-1)<c<u_R(-q_R+3ku_R-1)$ comes from the strict signs printed in (31)–(32); with the weak signs that optimality gives it reads $2q_Ru_R\le0$, which contradicts $q_R>0$ but not $q_R=0$. At $q_R=0$ the manufacturer is a single-product monopolist and $u_M=u_R$ is optimal when $u_R$ is her monopoly quality.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 37, proof of Proposition 7 (final contradiction)

import Mathlib
import Definitions.Def_QualityEncroach_NoCommit_Game

namespace QualityEncroach.NoCommit

/-- Proof of Proposition 7, p. 37: at a stage-3 history with `u_R > 0` and `q_R > 0`, no
optimal choice `(u_M, q_M)` of the manufacturer (over `u_M > 0`, `q_M ≥ 0`) sells directly
(`q_M > 0`) at the retailer's quality `u_M = u_R`. -/
theorem stage3_no_uniform (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR uM qM : ℝ)
    (huR : 0 < uR) (hqR : 0 < qR) (huM : 0 < uM) (hqM : 0 ≤ qM)
    (hopt : ∀ uM' qM' : ℝ, 0 < uM' → 0 ≤ qM' →
      mfrPayoff k c ⟨w, uR, qR, uM', qM'⟩ ≤ mfrPayoff k c ⟨w, uR, qR, uM, qM⟩) :
    ¬ (uM = uR ∧ 0 < qM) := by sorry

end QualityEncroach.NoCommit
