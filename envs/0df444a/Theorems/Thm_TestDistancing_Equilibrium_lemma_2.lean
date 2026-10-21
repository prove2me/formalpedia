-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_lemma_2
-- name    : TestDistancing.Equilibrium.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:19.976526+00:00
-- url     : https://prove2.me/theorems/34825f23-7295-4c87-8a37-97567e2cf7ac
-- title:
--   Lemma 2, corrected — a best response is 0 or 1 unless utility is constant in own activity
-- statement:
--   Fix agent $i$, the activities $x_{-i}\in[0,1]^{n-1}$ of all other agents, and a policy $(\alpha_L,\alpha_H)\in[0,1]^2$. Let $u_i(t)=u_i((t,x_{-i}),\alpha_L,\alpha_H)$ be the utility (1) of agent $i$ at activity $t$. If $t\in[0,1]$ is a best response, i.e. $u_i(s)\le u_i(t)$ for every $s\in[0,1]$, then
--
--   $$t\in\{0,1\}\quad\text{or}\quad u_i(s)=u_i(t)\ \text{for every } s\in[0,1].$$
--
--   So best responses are endpoints, except when the utility does not depend on the agent's own activity at all. **Formalization Note** The page states $x^e_i\in\{0,1\}$ without exception. That is false when $u_i$ is constant in $x_i$ (e.g. $v_i=0$ and $x_{-i}=\mathbf 0$, where $u_i\equiv-1/n-c\alpha_i$); the constant case is the only exception, because $u_i$ is convex in $x_i$ by Lemma 1(b).
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 10 (PDF 12), Lemma 2; p. 27 (PDF 29), proof

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- Lemma 2, corrected: a best response `t ∈ [0,1]` to other agents' activities in `[0,1]` is
`0` or `1`, unless the utility is constant in the agent's own activity on `[0,1]` (then every
activity level is a best response and the printed claim fails). -/
theorem lemma_2 (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      pureUtil P (Function.update x i s) α i ≤ pureUtil P (Function.update x i t) α i) :
    t = 0 ∨ t = 1 ∨
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        pureUtil P (Function.update x i s) α i = pureUtil P (Function.update x i t) α i := by sorry

end TestDistancing.Equilibrium
