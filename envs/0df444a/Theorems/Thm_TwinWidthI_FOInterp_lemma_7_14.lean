-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_lemma_7_14
-- name    : TwinWidthI.FOInterp.lemma_7_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:05.762031+00:00
-- url     : https://prove2.me/theorems/c29d9d8e-13d8-473f-9043-039d88471c66
-- title:
--   Lemma 7.14 — the pruned ℓ-shuffle of reducts MT′_ℓ(G, P, X) is a reduction of MT_ℓ(G, P)
-- statement:
--   Let $\ell>0$ and let $(G,\mathcal P)$ be a partitioned finite simple graph. For every part $X$ of $\mathcal P$ let $MT'_\ell(G,\mathcal P,X)$ be a reduct of $MT_\ell(G,\mathcal P,X)$, reductions performed in $(G,\mathcal P)$. Then the pruned $\ell$-shuffle of the family $\bigl(MT'_\ell(G,\mathcal P,X)\bigr)_{X\in\mathcal P}$ is a reduction of $MT_\ell(G,\mathcal P)$ in $(G,\mathcal P)$.
--
--   This is the central result of §7.3; in Section 8 it underlies the bound on the number of $E_{\ell+2}$-components inside a part (Lemma 8.5).
--
--   **Formalization Note.** The standing assumption $\ell>0$ of §7.3 is a hypothesis. The reducts are arbitrary (no uniqueness up to isomorphism is used).
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:38, Lemma 7.14 (standing assumption ℓ > 0 of §7.3, p. 3:35)

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem lemma_7_14 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (hℓ : 0 < ℓ) (F : Finset V → Set (List V))
    (hF : ∀ X ∈ P.parts, IsReduct G P (MTX G P ℓ X) (F X)) :
    IsReduction G P (MT V ℓ) (prunedShuffle G P ℓ F) := by sorry

end TwinWidthI.FOInterp
