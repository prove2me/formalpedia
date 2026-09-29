-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_lemma_4_1
-- name    : SetCoverThreshold.SetCover.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:59:11.861357+00:00
-- url     : https://prove2.me/theorems/78d1216f-f103-4566-8af8-653dd25d7a6f
-- title:
--   Lemma 4.1 — the set-cover gap: $kQ$ versus $(1-2f)\,kQ\ln m$
-- statement:
--   Assume the consequence of Raz's theorem (`RazRepetition`) and fix $\varepsilon>0$. There is $c>0$ (the constant of Lemma 2.3.1) such that the following holds for every 3CNF-5 formula $\varphi$, all $\ell,k,m,d$, every code of weight $\ell/2$ and pairwise distance $\ge\ell/3$, and every family of partition systems $B_r(m,2^\ell,k,d)$, one per random string $r$; consider the set-cover instance of Section 4 on $N=mR$ points.
--
--   1. If $\varphi$ is satisfiable, the $N$ points can be covered by $kQ$ subsets.
--   2. Let $f>0$ with $d\ge(1-f)\,k\ln m$ and
--   $$k^2\cdot 2^{-c\ell}\ <\ \frac{2\cdot 2f}{(k\ln m)^2}.$$
--   If only a $(1-\varepsilon)$-fraction of the clauses of $\varphi$ are simultaneously satisfiable, every cover uses at least
--   $$(1-2f)\,kQ\ln m$$
--   subsets.
--
--   This is the gap of the reduction: a factor of about $\ln m$ between the two cases, which the proof of Theorem 4.4 turns into $(1-\varepsilon)\ln N$.
--
--   **Formalization Note** "$f(k)\to 0$ as $k\to\infty$" is not formalized as a limit: $f$ is a parameter tied to $d$ by $d\ge(1-f)k\ln m$ (Lemma 3.2 gives $f=2/k$). "Sufficiently large ℓ" is replaced by the condition the proof itself uses (p. 647): $2\delta/(k\ln m)^2>k^2 2^{-c\ell}$ with $\delta=2f$.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 645, Lemma 4.1 (proof pp. 645–647; the ℓ condition from its last sentence, p. 647)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem lemma_4_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        ∀ P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d,
          (φ.toCNF.Satisfiable →
              ∃ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 ∧
                𝒞.card ≤ k * φ.numQuestions ℓ) ∧
            ∀ f : ℝ, 0 < f → (1 - f) * k * Real.log m ≤ d →
              (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) < 2 * (2 * f) / (k * Real.log m) ^ 2 →
                AtMostFracSat (1 - ε) φ.toCNF →
                  ∀ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 →
                    (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ 𝒞.card := by sorry

end SetCoverThreshold.SetCover
