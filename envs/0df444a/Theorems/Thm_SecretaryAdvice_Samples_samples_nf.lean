-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_samples_nf
-- name    : SecretaryAdvice.Samples.samples_nf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:00.82605+00:00
-- url     : https://prove2.me/theorems/a1d4e295-dcbd-4a1b-8440-bbf517201e67
-- title:
--   §5, p. 15 — the secretary problem with samples satisfies Non-Filtering (Definition 6)
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, let $X_j$ denote the information at round $j$ (the relative order of the samples and the first $j$ secretaries), $T_j$ the best-so-far event and $s_j$ the signal. For all rounds $j<i$, every value $x$ of the information at round $j$ and all signals $s,s'$,
--   $$\mathbb P[X_j=x,\,T_j,\,s_j=s']\cdot\mathbb P[T_j,\,s_j=s',\,T_i,\,s_i=s]=\mathbb P[X_j=x,\,T_j,\,s_j=s',\,T_i,\,s_i=s]\cdot\mathbb P[T_j,\,s_j=s'].$$
--   When the conditioning events have positive probability this is Definition 6: $\mathbb P[X_j=x\mid T_j,s_j]=\mathbb P[X_j=x\mid T_j,s_j,T_i,s_i]$. Later best-so-far events do not change what the algorithm has seen at round $j$.
--
--   Non-Filtering is the property that lets the LP constraint (4) be written with coefficients that do not depend on the policy.
--
--   **Formalization Note** Conditional probabilities are cross-multiplied, so the statement is meaningful also on null events. The information here is the full relative order of the samples and the first $j$ secretaries, which is finer than the pair $(\preceq_{1..j},s_1,\dots,s_j)$ of Definition 6; Non-Filtering for the finer information implies it for the coarser one. Rounds are 0-based in Lean.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, §5 LP Formulation (NF for Example 4); Definition 6, p. 8

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting

namespace SecretaryAdvice.Samples

theorem samples_nf (n k : ℕ) (i j : Fin n) (hji : j < i) (x : Info k j.val) (s s' : ℕ) :
    prob (fun σ : Outcome n k => info σ j = x ∧ T σ j ∧ sig σ j = s') *
        prob (fun σ : Outcome n k => T σ j ∧ sig σ j = s' ∧ T σ i ∧ sig σ i = s) =
      prob (fun σ : Outcome n k => info σ j = x ∧ T σ j ∧ sig σ j = s' ∧ T σ i ∧ sig σ i = s) *
        prob (fun σ : Outcome n k => T σ j ∧ sig σ j = s') := by sorry

end SecretaryAdvice.Samples
