-- Prove2me | Theorems.Thm_PosetSecretary_LowerBound_exists_perturbation_expectedScore_le
-- name    : PosetSecretary.LowerBound.exists_perturbation_expectedScore_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:00.679433+00:00
-- url     : https://prove2.me/theorems/defc48f5-d9ce-4c65-987e-9b7c886c3d59
-- title:
--   Proof of Proposition 5.1, p. 42, display — a perturbed scoring with OPT(I) = M and E[w(Alg(I))] ≤ (1+ε)OPT(I)/ω
-- statement:
--   Let $k\ge1$, $\omega\ge1$, and let $\mu$ be a selection rule with capacity $k$ on $\mathrm{Chains}(\omega,k)$. Let $i_0$ be a chain whose selection probabilities satisfy $\sum_j p^{i_0}_j\le k/\omega$, and let $M>0$ and $\varepsilon>0$. Then there is a scoring $w$ consistent with the order such that $\mathrm{OPT}(w,k)=M$ and
--   $$\mathbb E_\mu\big[w(\mathrm{Alg})\big]\le\frac{(1+\varepsilon)\,\mathrm{OPT}(w,k)}{\omega}.$$
--
--   This is the display of the proof of Proposition 5.1: the score is concentrated on the least-selected chain, and the remaining chains carry an arbitrarily small total score that only serves to make all scores distinct.
--
--   **Formalization Note** The statement is existential in the scoring. The page's middle inequality drops the term $\sum_jp^{i_0}_j\varepsilon^{i_0}_j$, which the page's constraints ($|\varepsilon^{i_0}_j|<M/2k$, $\sum_j\varepsilon^{i_0}_j=0$) do not make nonpositive; the bound holds for perturbations chosen small enough, not for every admissible one, and the existential form records exactly that. The scoring is chosen after $\mu$, as on the page, where $p^i_j$ is fixed before the scores.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.1, Appendix F, p. 42, third paragraph and display

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

namespace PosetSecretary.LowerBound

theorem exists_perturbation_expectedScore_le (ω k : ℕ) (hk : 1 ≤ k) (hω : 1 ≤ ω)
    (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) (i₀ : Fin ω)
    (hi₀ : ∑ j : Fin k, selProb μ ⟨i₀, j⟩ ≤ (k : ℝ) / ω) (M : ℝ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ChainsPoset ω k → ℝ, PosetSecretary.ProxyLabel.IsConsistentScoring w ∧ PosetSecretary.ProxyLabel.opt w k = M ∧
      expectedScore μ w ≤ (1 + ε) * PosetSecretary.ProxyLabel.opt w k / ω := by sorry

end PosetSecretary.LowerBound
