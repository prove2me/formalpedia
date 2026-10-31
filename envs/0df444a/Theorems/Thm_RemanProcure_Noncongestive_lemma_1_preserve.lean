-- Prove2me | Theorems.Thm_RemanProcure_Noncongestive_lemma_1_preserve
-- name    : RemanProcure.Noncongestive.lemma_1_preserve
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:12.471762+00:00
-- url     : https://prove2.me/theorems/b678592b-33c6-41a7-8cfc-f31ba7c82a87
-- title:
--   Lemma 1 (first sentence), p. 1445 — the operator T preserves the property set V^A
-- statement:
--   In the core acquisition model, let $\mathcal V^A$ be the set of functions $g:\mathbb N_0^K\to\mathbb R$ satisfying properties (A.1)–(A.6), and let $Tv(x)=\mu T_1v(x)+\lambda T_2v(x)+h(x)$. Then
--   $$v\in\mathcal V^A\ \Longrightarrow\ Tv\in\mathcal V^A .$$
--
--   This is the propagation step of the structural analysis: combined with value iteration it shows that the optimal cost function has properties (A.1)–(A.6).
--
--   **Formalization Note** The standing assumptions of §2 are hypotheses, including the disclosed additions $K\ge1$, $p$ a probability vector, $r_i\ge0$, $c_A\ge0$, $\mu,\lambda>0$.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), p. 1445 (PDF 6), Lemma 1 (first sentence)

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

namespace RemanProcure.Noncongestive
theorem lemma_1_preserve {K : ℕ} (P : Params K) (hP : Standing P) (v : (Fin K → ℕ) → ℝ) (hv : VA P v) : VA P (T P v) := by sorry
end RemanProcure.Noncongestive
