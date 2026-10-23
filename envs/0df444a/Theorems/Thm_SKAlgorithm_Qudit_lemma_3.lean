-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_lemma_3
-- name    : SKAlgorithm.Qudit.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:58.929589+00:00
-- url     : https://prove2.me/theorems/91ae80d6-3405-4524-80f0-eaca0c35ae26
-- title:
--   Lemma 3, p. 12 — the group commutator of exp(iF), exp(iG) is exp(i·i[F,G]) up to O(δ³)
-- statement:
--   There is a constant $c_1 > 0$ with the following property. Let $F$ and $G$ be Hermitian $d \times d$ matrices (any $d$) with $\|F\|, \|G\| < \delta$. Then
--   $$d\big(\exp(iF)\exp(iG)\exp(-iF)\exp(-iG),\ \exp(i \times i[F, G])\big) \le c_1 \delta^3 ,$$
--   where $[F, G] = FG - GF$.
--
--   The paper gives $c_1 \approx 4$. With Lemma 2 this shows that a gate near the identity is approximated to third order by a group commutator of two gates closer to the identity.
--
--   **Formalization Note.** The constant $c_1$ is existential and is chosen before the dimension $d$ and the matrices: the paper's "some constant $c_1 \approx 4$" is a number, not a function of $d$. The value $4$ is not pinned. The exponential is `NormedSpace.exp`, and $\exp(i \times i[F,G])$ is kept in the paper's form `exp (I • (I • (F * G - G * F)))`.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 12, §5.2, Lemma 3, Eq. (32)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem lemma_3 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (d : ℕ) (F G : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ),
      F.IsHermitian → G.IsHermitian → specNorm F < δ → specNorm G < δ →
      specNorm (NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
          NormedSpace.exp ((-Complex.I) • F) * NormedSpace.exp ((-Complex.I) • G) -
        NormedSpace.exp (Complex.I • (Complex.I • (F * G - G * F)))) ≤ c₁ * δ ^ 3 := by sorry

end SKAlgorithm.Qudit
