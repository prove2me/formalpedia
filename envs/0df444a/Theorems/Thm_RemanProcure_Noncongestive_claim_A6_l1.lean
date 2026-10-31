-- Prove2me | Theorems.Thm_RemanProcure_Noncongestive_claim_A6_l1
-- name    : RemanProcure.Noncongestive.claim_A6_l1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:20.549984+00:00
-- url     : https://prove2.me/theorems/78c4c075-2017-400b-b1bc-1407461733c5
-- title:
--   §3, p. 1445, (A.6) at l = 1 — acquiring a core is more costly after a low-quality core is replaced by a high-quality one
-- statement:
--   In the core acquisition model, let $\Delta(x)=c_A+\sum_{i=1}^K p_i v^*(x+e_i)-v^*(x)$ be the acquisition gap of the optimal cost function. Then for every state $x$ and types $q<w$ (type $q$ of higher quality than type $w$),
--   $$\Delta(x+e_w)\le\Delta(x+e_q).$$
--
--   This is the paper's reading of property (A.6) at $l=1$: holding a higher-quality core in place of a lower-quality one makes acquisition weakly more costly.
--
--   **Formalization Note** The standing assumptions of §2 are hypotheses, including the disclosed additions $K\ge1$, $p$ a probability vector, $r_i\ge0$, $c_A\ge0$, $\mu,\lambda>0$. Type 1 is index $0$ of `Fin K`, so "$q<w$" is the order on `Fin K`.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), p. 1445 (PDF 6), §3, "Property (A.6) implies that, when l = 1, it is more costly to acquire a core if there are more high-quality cores and fewer low-quality cores."

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

namespace RemanProcure.Noncongestive
theorem claim_A6_l1 {K : ℕ} (P : Params K) (hP : Standing P) : ∀ (x : Fin K → ℕ) (q w : Fin K), q < w → acqGap P (x + e w) ≤ acqGap P (x + e q) := by sorry
end RemanProcure.Noncongestive
