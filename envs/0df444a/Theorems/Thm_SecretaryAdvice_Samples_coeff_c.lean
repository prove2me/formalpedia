-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_coeff_c
-- name    : SecretaryAdvice.Samples.coeff_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:00.346205+00:00
-- url     : https://prove2.me/theorems/ce3abd7b-42a1-4b4f-af98-6f5a6119632e
-- title:
--   §5, p. 15 — c(i,s,j,s′) = P(T_j, s_j = s′ | T_i, s_i = s) = 1/(s+1)·∏_{t=1}^{j−1} (s′+t)/(s+t+1) for j < i, s′ ≤ s
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, let $j<i$ be rounds (numbered from 1) and $s,s'$ signals. Then
--   $$\mathbb P(T_j,\,s_j=s',\,T_i,\,s_i=s)=c(i,s,j,s')\cdot\mathbb P(T_i,\,s_i=s),$$
--   where $c(i,s,j,s')=\dfrac{1}{s+1}\displaystyle\prod_{t=1}^{j-1}\frac{s'+t}{s+t+1}$ if $s'\le s$ and $c(i,s,j,s')=0$ if $s'>s$. In conditional form, $c(i,s,j,s')=\mathbb P(T_j,s_j=s'\mid T_i,s_i=s)$.
--
--   These are the constraint coefficients of the samples LP.
--
--   **Formalization Note** Cross-multiplied, so no division by a possibly null probability appears. Lean rounds $i,j$ are 0-based and enter the formula as $i+1$, $j+1$. The statement holds for all natural $s,s'$; outside the signal space both sides vanish.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, §5 LP Formulation, formula for c(i, s, j, s′)

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting
import Definitions.Def_SecretaryAdvice_Samples_LP

namespace SecretaryAdvice.Samples

theorem coeff_c (n k : ℕ) (i j : Fin n) (hji : j < i) (s s' : ℕ) :
    prob (fun σ : Outcome n k => T σ j ∧ sig σ j = s' ∧ T σ i ∧ sig σ i = s) =
      cCoef (i.val + 1) s (j.val + 1) s' * prob (fun σ : Outcome n k => T σ i ∧ sig σ i = s) := by sorry

end SecretaryAdvice.Samples
