-- Prove2me | Theorems.Thm_PersuadeEarly_Private_lemma_4
-- name    : PersuadeEarly.Private.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:21.91311+00:00
-- url     : https://prove2.me/theorems/c47cf991-7541-44e1-9271-7b778948e286
-- title:
--   Lemma 4, p. 44 (corrected reading) — if $\bar F(p_2)>q_L$, then $\bar D(p_1,p_2)\le\bar D(\bar F^{-1}(q_L),p_2)$
-- statement:
--   Under the standing assumptions, let $0\le p_2<p_1$ with $\bar F(p_2)>q_L$. Then
--   $$\bar D(p_1,p_2)\le\bar D\big(\bar F^{-1}(q_L),p_2\big).$$
--
--   The paper states Lemma 4 as: "the optimal solution to (A.18) is such that either (a) $\bar F(p_2)\le q_L$ or (b) $\bar F(p_1)=q_L$". Its proof (pp. 46–50) shows that whenever $\bar F(p_2)>q_L$, moving $p_1$ to the price at which the low-type firm exactly sells out in period 1 does not lower the value; that is the statement here. It is what the proof of Theorem 2 uses.
--
--   **Formalization Note** As printed, "the optimal solution … is such that" fails at ties: for uniform valuations on $[0,1]$, $q_L=0.2$, $P(H)=0.8$ and $p_2=0.5$, every $p_1\in[0.6,0.8]$ attains the optimum $0.236$, with $\bar F(p_2)>q_L$ and $\bar F(p_1)\ne q_L$. The weak form is stated instead. $p_2<p_1$ is implicit in (A.16)–(A.18).
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 44, Lemma 4; proof pp. 46–50

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_AppendixA

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 44, Lemma 4 (corrected reading): "The optimal solution to (A.18) is such that either:
(a) F̄(p2) ≤ qL or (b) F̄(p1) = qL."

Stated as the claim its proof (pp. 46–50) establishes: for prices `0 ≤ p2 < p1` with
`F̄(p2) > qL`, moving `p1` to `F̄^{-1}(qL)` does not lower the value, `D̄(p1, p2) ≤ D̄(F̄^{-1}(qL), p2)`.

**Formalization Note** As printed ("the optimal solution … is such that") the lemma fails at ties:
for uniform valuations on `[0, 1]`, `qL = 0.2`, `P(H) = 0.8`, `p2 = 0.5`, every `p1 ∈ [0.6, 0.8]`
attains the optimum `0.236` with `F̄(p2) > qL` and `F̄(p1) ≠ qL`. The weak form here is what the
proof of Theorem 2 uses. `p2 < p1` is implicit in (A.16)–(A.18). -/
theorem lemma_4 (M : Model) (hM : M.Standing) :
    ∀ p1 p2 : ℝ, 0 ≤ p2 → p2 < p1 → M.qL < M.Fbar p2 →
      Dbar M p1 p2 ≤ Dbar M (M.FbarInv M.qL) p2 := by sorry

end PersuadeEarly.Private
