-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_pinsker_display
-- name    : UniformDRO.LowerBound.pinsker_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:53.572221+00:00
-- url     : https://prove2.me/theorems/543b68fd-a17f-4e55-b3a7-5d2782ea4afc
-- title:
--   Proof of Thm 3 (App. D.1), p. 46 — Pinsker for n-fold products: ‖P₁ⁿ − P₂ⁿ‖²_TV ≤ (n/2) D_kl(P₂‖P₁)
-- statement:
--   Let $n \ge 0$, let $P_1$ and $P_2$ be the laws on $\{0, M\}$ with masses $p_1 \in (0,1)$ and $p_2 \in [0,1]$ at $M$, and let $P_1^n, P_2^n$ be their $n$-fold products. Then
--   $$\|P_1^n - P_2^n\|_{\mathrm{TV}}^2 \le \frac n2\, D_{\mathrm{kl}}(P_2\|P_1).$$
--
--   This is Pinsker's inequality combined with the additivity of the Kullback–Leibler divergence over independent coordinates; it converts the one-observation bounds of the two KL displays into the bound $\|P_1^n - P_2^n\|_{\mathrm{TV}} \le \tfrac12$ needed in (37).
--
--   **Formalization Note.** The total variation is the half-$\ell^1$ distance on $\{0,M\}^n$ from the mission's definition file, and $D_{\mathrm{kl}}(P_2\|P_1)$ is the platform's Bernoulli relative entropy $d(p_2, p_1)$. The hypothesis $p_1 \in (0,1)$ keeps the divergence finite, where the real-valued formula is the true divergence; it holds wherever the page applies the inequality (in the second branch the roles of the two laws are exchanged, which the symmetry of total variation allows).
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 3 (App. D.1), p. 46, Pinsker step

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem pinsker_display (n : ℕ) (p₁ p₂ : ℝ) (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) :
    tvDist n p₁ p₂ ^ 2 ≤ n / 2 * BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by sorry

end UniformDRO.LowerBound
