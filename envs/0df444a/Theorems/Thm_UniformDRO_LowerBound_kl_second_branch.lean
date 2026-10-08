-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_kl_second_branch
-- name    : UniformDRO.LowerBound.kl_second_branch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:07.991506+00:00
-- url     : https://prove2.me/theorems/702937df-7f4c-4c19-91c3-99cebf2da281
-- title:
--   Proof of Thm 3 (App. D.1), p. 46 — D_kl(P₁‖P₂) = −log(1 − δ) ≤ δ/(1 − δ) ≤ 2δ for δ ≤ ½
-- statement:
--   Let $0 < \delta \le \tfrac12$. Let $P_1$ be the point mass at $0$ (the law of $Z_1 \equiv 0$) and $P_2$ the law on $\{0, M\}$ with mass $\delta$ at $M$. Then
--   $$D_{\mathrm{kl}}(P_1\|P_2) = -\log(1-\delta) \le \frac{\delta}{1-\delta} \le 2\delta .$$
--
--   This bounds the information in one observation for the $n^{-1/k_*}$ branch of Theorem 3.
--
--   **Formalization Note.** $D_{\mathrm{kl}}(P_1\|P_2)$ is the platform's Bernoulli relative entropy $d(0, \delta) = 0\cdot\log(0/\delta) + 1\cdot\log(1/(1-\delta))$, where $0 \log 0 = 0$ is the standard convention. Stated as three conjuncts, one per relation of the chain.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 3 (App. D.1), p. 46, second-branch KL display

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem kl_second_branch (δ : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    BanditAlgorithm.bernoulliRelativeEntropy 0 δ = -Real.log (1 - δ) ∧
      -Real.log (1 - δ) ≤ δ / (1 - δ) ∧ δ / (1 - δ) ≤ 2 * δ := by sorry

end UniformDRO.LowerBound
