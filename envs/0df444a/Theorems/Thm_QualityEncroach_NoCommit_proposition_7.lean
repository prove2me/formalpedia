-- Prove2me | Theorems.Thm_QualityEncroach_NoCommit_proposition_7
-- name    : QualityEncroach.NoCommit.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:38.986386+00:00
-- url     : https://prove2.me/theorems/5cee71c9-cdb6-4133-bc42-6d8a9de32879
-- title:
--   Proposition 7, p. 21 — without quality commitment in the direct channel, quality differentiation across channels is always optimal
-- statement:
--   Consider the supply chain of §6.3: consumers with quality sensitivity uniform on $[0,1]$, unit cost $kv^2$ for quality $v$ ($k>0$), direct selling cost $c\ge0$, and the timing (i) the manufacturer announces the retailer's quality $u_R$ and the wholesale price $w$; (ii) the retailer orders $q_R$; (iii) the manufacturer chooses the direct-channel quality $u_M$ and quantity $q_M$. Because $u_M$ is chosen after the retailer's order, the manufacturer cannot commit to the quality of the direct-channel product.
--
--   Let $\sigma$ be a subgame perfect equilibrium of this game, and suppose that on the equilibrium path the manufacturer encroaches ($q_M>0$) and the retailer orders ($q_R>0$). Then the two channels carry products of different quality:
--   $$
--   u_M \neq u_R .
--   $$
--
--   The paper states this as: *if the encroaching manufacturer cannot commit to a level of quality in the direct-channel product, then quality differentiation across channels is always optimal.* It contrasts with Proposition 4 of the same paper, where under commitment uniform quality can be optimal.
--
--   **Formalization Note.** "Across channels" is read as both channels selling, hence the hypothesis $q_R>0$ on the path; the paper's proof also needs it (see the stage-3 item). The statement concerns every subgame perfect equilibrium; the paper does not prove that one exists, and neither does this statement.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 21, §6.3, Proposition 7; proof p. 37

import Mathlib
import Definitions.Def_QualityEncroach_NoCommit_Game

namespace QualityEncroach.NoCommit

/-- **Proposition 7** (p. 21). If the encroaching manufacturer cannot commit to the quality of
the direct-channel product, then in every subgame perfect equilibrium in which she encroaches
(`q_M > 0`) and the retailer orders (`q_R > 0`), the two channels carry different qualities. -/
theorem proposition_7 (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile) (hσ : IsSPE k c σ)
    (henc : Encroaches σ) (hR : 0 < σ.path.qR) :
    σ.path.uM ≠ σ.path.uR := by sorry

end QualityEncroach.NoCommit
