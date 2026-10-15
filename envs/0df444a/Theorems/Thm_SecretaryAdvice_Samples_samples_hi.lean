-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_samples_hi
-- name    : SecretaryAdvice.Samples.samples_hi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:59.543408+00:00
-- url     : https://prove2.me/theorems/f7d7d47c-c6b5-4bf4-93dd-7e4cb8989c15
-- title:
--   §5, p. 15 — the secretary problem with samples satisfies History-Irrelevance (Definition 7)
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, let $X_i$ be the information at round $i$, $T_i$ the best-so-far event, $s_i$ the signal and $r_i=n$ the event that the secretary of round $i$ is the best of the $n$ secretaries. For every round $i$, every value $x$ of the information and every signal $s$,
--   $$\mathbb P[X_i=x,\,r_i=n,\,T_i,\,s_i=s]\cdot\mathbb P[T_i,\,s_i=s]=\mathbb P[X_i=x,\,T_i,\,s_i=s]\cdot\mathbb P[r_i=n,\,T_i,\,s_i=s].$$
--   That is, conditioned on $(T_i,s_i)$ the information $X_i$ and the event $r_i=n$ are independent (Definition 7).
--
--   History-Irrelevance lets the winning probability of a policy be written through $a(i,s)=\mathbb P[r_i=n,s_i=s]$ alone, giving the LP objective (5).
--
--   **Formalization Note** Independence is stated in cross-multiplied form. Since $r_i=n$ implies $T_i$, the events $r_i=n$ and $(r_i=n)\wedge T_i$ coincide. The information is the full relative order of the samples and the first $i$ secretaries (finer than in Definition 7, which makes the statement stronger). Rounds are 0-based in Lean.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, §5 LP Formulation (HI for Example 4); Definition 7, p. 8

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting

namespace SecretaryAdvice.Samples

theorem samples_hi (n k : ℕ) (i : Fin n) (x : Info k i.val) (s : ℕ) :
    prob (fun σ : Outcome n k => info σ i = x ∧ top σ i ∧ T σ i ∧ sig σ i = s) *
        prob (fun σ : Outcome n k => T σ i ∧ sig σ i = s) =
      prob (fun σ : Outcome n k => info σ i = x ∧ T σ i ∧ sig σ i = s) *
        prob (fun σ : Outcome n k => top σ i ∧ T σ i ∧ sig σ i = s) := by sorry

end SecretaryAdvice.Samples
