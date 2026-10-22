-- Prove2me | Theorems.Thm_PosetSecretary_LowerBound_opt_perturbation_eq
-- name    : PosetSecretary.LowerBound.opt_perturbation_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:21.985855+00:00
-- url     : https://prove2.me/theorems/4f108a26-1b4d-46f3-88e4-7b341660a289
-- title:
--   Proof of Proposition 5.1, p. 42 — for the perturbed scoring w = w′ + ε of Figure 8, OPT(I) = M
-- statement:
--   Let $k\ge1$, $\omega\ge0$, $M>0$, and let $i_0$ be one of the $\omega$ chains of $\mathrm{Chains}(\omega,k)$. Let $w$ be a scoring consistent with the order (nonnegative, distinct, increasing along each chain) which is a perturbation of
--   $$w'(i,j)=\begin{cases}M/k,& i=i_0,\\ 0,& i\ne i_0,\end{cases}$$
--   in the following sense:
--
--   1. on every chain $i\ne i_0$: $0\le w(i,j)<\dfrac{M}{2k}$;
--   2. on the chain $i_0$: $\Big|w(i_0,j)-\dfrac Mk\Big|<\dfrac{M}{2k}$ for all $j$;
--   3. $\displaystyle\sum_j\Big(w(i_0,j)-\frac Mk\Big)=0$.
--
--   Then the offline optimum with $k$ selections is
--   $$\mathrm{OPT}(w,k)=M .$$
--
--   The perturbation makes the scores distinct without moving the optimum away from the heavy chain $i_0$.
--
--   **Formalization Note** The page's further constraint $\sum_{i<\omega,j}\varepsilon^i_j\le\varepsilon M/\omega$ is not needed for this claim and is omitted. Distinctness is part of consistency. The hypothesis $k\ge1$ is necessary: for $k=0$ the poset is empty and the optimum is $0$.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.1, Appendix F, p. 42, third paragraph

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

namespace PosetSecretary.LowerBound

theorem opt_perturbation_eq (ω k : ℕ) (hk : 1 ≤ k) (i₀ : Fin ω) (M : ℝ) (hM : 0 < M)
    (w : ChainsPoset ω k → ℝ) (hw : PosetSecretary.ProxyLabel.IsConsistentScoring w)
    (hlight : ∀ (i : Fin ω) (j : Fin k), i ≠ i₀ → 0 ≤ w ⟨i, j⟩ ∧ w ⟨i, j⟩ < M / (2 * k))
    (hheavy : ∀ j : Fin k, |w ⟨i₀, j⟩ - M / k| < M / (2 * k))
    (hsum : ∑ j : Fin k, (w ⟨i₀, j⟩ - M / k) = 0) :
    PosetSecretary.ProxyLabel.opt w k = M := by sorry

end PosetSecretary.LowerBound
