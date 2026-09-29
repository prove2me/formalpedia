-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_prop_4_3
-- name    : SetCoverThreshold.SetCover.prop_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:58:40.0384+00:00
-- url     : https://prove2.me/theorems/5f014a0c-314f-4966-99f1-def1f7ec3ab2
-- title:
--   Proposition 4.3 — a small cover yields a strategy weakly accepted with probability $\ge 2\delta/(k\ln m)^2$
-- statement:
--   Consider the set-cover instance of Section 4 built from a 3CNF-5 formula $\varphi$, parameters $\ell,k$, a code of weight $\ell/2$ and distance $\ell/3$, and partition systems $B_r(m,2^\ell,k,d)$, one for each random string $r$. Let $\delta>0$ with
--
--   $$(1-\delta/2)\,k\ln m\ \le\ d .$$
--
--   Let $\mathcal C$ be a collection of subsets that covers all $N=mR$ points, with $|\mathcal C|\le(1-\delta)\,kQ\ln m$. Then for some (deterministic) strategy of the $k$ provers the verifier weakly accepts with probability at least
--
--   $$\frac{2\delta}{(k\ln m)^2}.$$
--
--   Combined with Lemma 2.3.1, this shows that for unsatisfiable-far formulas no small cover exists.
--
--   **Formalization Note** "|𝒞| = (1 − δ)kQ ln m" is read as $\le$ (see Proposition 4.2). The paper's "by our choice of δ = 2f(k)" is used in the proof only through $(1-\delta/2)k\ln m\le d$, which is taken as the hypothesis. The paper's randomized strategy is a proof device; fixing its coins gives the deterministic strategy asserted here.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 646, Proposition 4.3

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem prop_4_3 (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (δ : ℝ) (hδ : 0 < δ) (hd : (1 - δ / 2) * k * Real.log m ≤ d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    ∃ A : φ.KStrategy ℓ k, 2 * δ / (k * Real.log m) ^ 2 ≤ φ.weakAcceptFrac code A := by sorry

end SetCoverThreshold.SetCover
