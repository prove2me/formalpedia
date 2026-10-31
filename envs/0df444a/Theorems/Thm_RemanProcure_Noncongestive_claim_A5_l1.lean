-- Prove2me | Theorems.Thm_RemanProcure_Noncongestive_claim_A5_l1
-- name    : RemanProcure.Noncongestive.claim_A5_l1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:27.306406+00:00
-- url     : https://prove2.me/theorems/75429a40-524d-4ff4-8014-075c7d71f618
-- title:
--   §3, p. 1445, (A.5) at l = 1 — acquiring a core is more costly when there are more cores of any type
-- statement:
--   In the core acquisition model, let $\Delta(x)=c_A+\sum_{i=1}^K p_i v^*(x+e_i)-v^*(x)$ be the acquisition gap of the optimal cost function in state $x$ (acquiring is optimal when $\Delta(x)\le0$). Then for every state $x$ and every type $q$,
--   $$\Delta(x)\le\Delta(x+e_q).$$
--
--   This is the paper's reading of property (A.5) at $l=1$: one more core of any type makes acquisition weakly more costly. It is the source of the threshold form of the optimal acquisition policy.
--
--   **Formalization Note** The standing assumptions of §2 are hypotheses, including the disclosed additions $K\ge1$, $p$ a probability vector, $r_i\ge0$, $c_A\ge0$, $\mu,\lambda>0$. Type 1 is index $0$ of `Fin K`.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), p. 1445 (PDF 6), §3, "Property (A.5) implies that, when l = 1, it is more costly to acquire a core if there are more cores of any type."

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

namespace RemanProcure.Noncongestive
theorem claim_A5_l1 {K : ℕ} (P : Params K) (hP : Standing P) : ∀ (x : Fin K → ℕ) (q : Fin K), acqGap P x ≤ acqGap P (x + e q) := by sorry
end RemanProcure.Noncongestive
