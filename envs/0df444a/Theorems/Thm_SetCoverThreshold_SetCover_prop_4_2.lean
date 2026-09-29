-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_prop_4_2
-- name    : SetCoverThreshold.SetCover.prop_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:58:01.212449+00:00
-- url     : https://prove2.me/theorems/64f1a5aa-caa8-4c7d-ac86-5c79b1c89c03
-- title:
--   Proposition 4.2 — the fraction of good random strings is at least $\delta/2$
-- statement:
--   Consider the set-cover instance of Section 4 built from a 3CNF-5 formula $\varphi$, parameters $\ell$ and $k\ge 1$, a code of weight $\ell/2$ and distance $\ell/3$, and $m\ge 2$. The paper sets up (p. 646): "Let 𝒞 be a collection of subsets that covers S, where |𝒞| = (1 − δ)kQ ln m. With each question q to a prover P_i associate a weight w_{q,i} equal to the number of answers a such that S_(q,a,i) ∈ 𝒞. Hence, Σ_{q,i} w_{q,i} = |𝒞|. With each random string r associate a weight w_r = Σ_{(q,i)∈r} w_{q,i}. This weight is equal to the number of subsets that participate in covering the m points of B_r(m, L, k, d). Call r good if w_r < (1 − δ/2)k ln m."
--
--   Let $0<\delta\le 1$ and let $\mathcal C$ be a collection of subsets with $|\mathcal C|\le(1-\delta)\,kQ\ln m$. Then
--
--   $$\frac{\#\{r:\ w_r<(1-\delta/2)\,k\ln m\}}{R}\ \ge\ \frac{\delta}{2},$$
--
--   where $R$ is the number of random strings. It is the averaging step of the soundness analysis of the reduction.
--
--   **Formalization Note** The page's "$|\mathcal C|=(1-\delta)kQ\ln m$" is read as $\le$: the left side is an integer and the right side is in general irrational, so the literal equation would make the statement nearly vacuous, and the proof uses only $\le$. The proposition does not need $\mathcal C$ to be a cover.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 646, Proposition 4.2 (with the definitions of w_{q,i}, w_r and good r before it)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem prop_4_2 (φ : Formula5) (ℓ k m : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (hk : 0 < k) (hm : 2 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒞 : Finset (φ.SetIdx code))
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    δ / 2 ≤
      ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
          (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * k * Real.log m)).card : ℝ) /
        Fintype.card (φ.RandomString ℓ) := by sorry

end SetCoverThreshold.SetCover
