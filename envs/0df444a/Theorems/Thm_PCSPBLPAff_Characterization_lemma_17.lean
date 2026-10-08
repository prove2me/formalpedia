-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_17
-- name    : PCSPBLPAff.Characterization.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:03.135983+00:00
-- url     : https://prove2.me/theorems/a886ec78-cf4f-4ed4-b30d-d3d275b9c533
-- title:
--   Lemma 17 for M = M_BLP+Aff, p. 15 — F_{M_BLP+Aff}(A) → B iff M_BLP+Aff has a minion homomorphism to Pol(A, B)
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a promise template on finite domains. The following are equivalent:
--
--   1. the free structure $F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)$ admits a homomorphism to $\mathbf B$;
--   2. there exists a minion homomorphism from $\mathcal M_{\mathrm{BLP+Aff}}$ to $\mathrm{Pol}(\mathbf A,\mathbf B)$.
--
--   $$F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)\to\mathbf B\iff \mathcal M_{\mathrm{BLP+Aff}}\to\mathrm{Pol}(\mathbf A,\mathbf B).$$
--
--   This is the fundamental property of free structures ([BBKO19, Lemma 4.4]) and the last step of the proof of Lemma 7.
--
--   **Formalization Note** The page states the lemma for an arbitrary minion $\mathcal M$; this item is its specialization to $\mathcal M=\mathcal M_{\mathrm{BLP+Aff}}$, the only case the mission uses.
-- source:
--   arXiv:1907.04383v3, Lemma 17, p. 15 (citing [BBKO19, Lemma 4.4]), specialized to M = M_BLP+Aff

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Lemma 17 ([BBKO19, Lemma 4.4]), p. 15, for the minion `M = M_BLP+Aff`: for a promise
template `(𝔸, 𝔹)`, the free structure `F_{M_BLP+Aff}(𝔸)` has a homomorphism to `𝔹` iff
`M_BLP+Aff` admits a minion homomorphism to `Pol(𝔸, 𝔹)`. -/
theorem lemma_17 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    (∃ σ : FreeDom A → B, PCSPBLPAff.Symmetric.IsHom (freeStruct 𝔸) 𝔹 σ) ↔ HasMinionHomToPol 𝔸 𝔹 := by sorry

end PCSPBLPAff.Characterization
