-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_eq_2
-- name    : SecretaryAdvice.Memoryless.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:47.437013+00:00
-- url     : https://prove2.me/theorems/7f7e9377-dfba-4840-8d87-82a6212549fa
-- title:
--   Equation (2), p. 8 — under HI, P[r_i = n | ≺_{1..i}, s_1, …, s_i] = P[r_i = n | T_i, s_i]
-- statement:
--   Let $\mathbb P$ be a signaling structure satisfying History-Irrelevance. Fix a round $i$ and a value $x$ of the information $(\prec_{1..i},s_1,\dots,s_i)$ available at round $i$; $x$ determines whether $T_i$ holds and the current signal $s_i$. Then
--   $$\mathbb P[r_i=n\mid \prec_{1..i},s_1,\dots,s_i]=\mathbb P[r_i=n\mid T_i,s_i],\tag{2}$$
--   where on the right $T_i$ and $s_i$ take the values determined by $x$.
--
--   This is the first consequence of HI drawn in §2.2: to know the probability that $i$ is the top secretary it suffices to know its signal and whether it is best so far. It is used in the computation of the objective (5).
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The conditional equality is stated cross-multiplied: $\mathbb P[r_i=n,\ \text{info}=x]\cdot\mathbb P[T_i=t,\ s_i=s]=\mathbb P[\text{info}=x]\cdot\mathbb P[r_i=n,\ T_i=t,\ s_i=s]$ with $t,s$ read off $x$, so null conditioning events impose nothing.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 8, §2.2, equation (2)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting

namespace SecretaryAdvice.Memoryless

/-- Equation (2), p. 8: under HI, `P[r_i = n | ≺_{1..i}, s_1, …, s_i] = P[r_i = n | T_i, s_i]`,
cross-multiplied; the values of `T_i` and `s_i` are those determined by the information `x`. -/
theorem eq_2 {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hHI : HistoryIrrelevance μ) (i : Fin n) (x : Info n S i) :
    prob μ (fun ω => IsTop i ω ∧ info i ω = x) *
        prob μ (fun ω => (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) =
      prob μ (fun ω => info i ω = x) *
        prob μ (fun ω => IsTop i ω ∧ (T i ω ↔ bestSoFar x = true) ∧ sig i ω = lastSignal x) := by sorry

end SecretaryAdvice.Memoryless
