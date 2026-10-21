-- Prove2me | Theorems.Thm_TechFinConstr_Selection_lemma_A_1
-- name    : TechFinConstr.Selection.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:12.798302+00:00
-- url     : https://prove2.me/theorems/5fa90216-43ce-401c-ac59-2940e8f518ec
-- title:
--   Lemma A.1, p. 38 — every type in 𝒫 has p₀ < q₀ and pₙ ≥ qₙ
-- statement:
--   Consider the economy of Starmans' model: states $\Omega=\{0,\dots,n\}$, cash flows $0=x_0<\dots<x_n$, baseline distribution $q$ with $q_i>0$, expected value of effort $\pi>0$, and the type set $\mathscr P$ of distributions $p$ satisfying Assumptions 1–3. Then every type $p\in\mathscr P$ puts strictly less mass than $q$ on the lowest state and at least as much mass as $q$ on the highest state:
--   $$p_0<q_0\qquad\text{and}\qquad p_n\ge q_n .$$
--
--   This is the first step of the paper's sign analysis of the likelihood ratio $\varphi(p)$ (Lemma 2): it guarantees that some state has $p_i>q_i$, so that $\bar\iota(p)$ is well defined.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 38, Appendix A.2, Lemma A.1

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem lemma_A_1 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p) :
    p 0 < E.q 0 ∧ E.q (Fin.last n) ≤ p (Fin.last n) := by sorry

end TechFinConstr.Selection
