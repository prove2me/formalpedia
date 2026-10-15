-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_eq_3
-- name    : SecretaryAdvice.Memoryless.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:00.443278+00:00
-- url     : https://prove2.me/theorems/3623a819-548e-4fa8-a4a8-25a94c64a664
-- title:
--   Equation (3), p. 9 — under HI, P[X | s_i, r_i = n] = P[X | T_i, s_i] for every event X of the round-i information
-- statement:
--   Let $\mathbb P$ be a signaling structure satisfying History-Irrelevance. Fix a round $i$, a signal value $s$, and an event $X$ that depends only on the information $(\prec_{1..i},s_1,\dots,s_i)$ available at round $i$ (that is, $X=\{(\prec_{1..i},s_1,\dots,s_i)\in A\}$ for a set $A$ of information values). Then
--   $$\mathbb P[X\mid s_i=s,\ r_i=n]=\mathbb P[X\mid T_i,\ s_i=s].\tag{3}$$
--
--   This is the second consequence of HI drawn in §2.2 (it uses that $r_i=n$ implies $T_i$). It is the step of the proof of Proposition 10 that turns the conditional picking probability given $r_i=n$ into $z(i,s)$.
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The conditional equality is stated cross-multiplied: $\mathbb P[X,\ s_i=s,\ r_i=n]\cdot\mathbb P[T_i,\ s_i=s]=\mathbb P[X,\ T_i,\ s_i=s]\cdot\mathbb P[s_i=s,\ r_i=n]$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 9, §2.2, equation (3)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting

namespace SecretaryAdvice.Memoryless

/-- Equation (3), p. 9: under HI, for every event `X = {info_i ∈ A}` determined by the
information at round `i`, `P[X | s_i, r_i = n] = P[X | T_i, s_i]`, cross-multiplied. -/
theorem eq_3 {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hHI : HistoryIrrelevance μ) (i : Fin n) (A : Set (Info n S i)) (s : S) :
    prob μ (fun ω => info i ω ∈ A ∧ sig i ω = s ∧ IsTop i ω) *
        prob μ (fun ω => T i ω ∧ sig i ω = s) =
      prob μ (fun ω => info i ω ∈ A ∧ T i ω ∧ sig i ω = s) *
        prob μ (fun ω => sig i ω = s ∧ IsTop i ω) := by sorry

end SecretaryAdvice.Memoryless
