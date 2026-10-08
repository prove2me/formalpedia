-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_7
-- name    : PCSPBLPAff.Characterization.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:47.330977+00:00
-- url     : https://prove2.me/theorems/5a6697b2-febb-4ab7-8964-669407abbd4b
-- title:
--   Lemma 7, p. 11 — BLP+Affine correctly solves PCSP-Decision(A, B) iff M_BLP+Aff has a minion homomorphism to Pol(A, B)
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a promise template on finite domains. The following are equivalent:
--
--   1. the BLP+Affine algorithm correctly solves $\mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B)$ (Definition 1);
--   2. $\mathcal M_{\mathrm{BLP+Aff}}$ admits a minion homomorphism to $\mathrm{Pol}(\mathbf A,\mathbf B)$.
--
--   $$\text{BLP+Affine correctly solves }\mathrm{PCSP}(\mathbf A,\mathbf B)\iff \mathcal M_{\mathrm{BLP+Aff}}\to\mathrm{Pol}(\mathbf A,\mathbf B).$$
--
--   This is the algebraic characterization of the algorithm's power; Lemmas 8 and 9 translate its right-hand side into concrete polymorphisms, giving Theorem 4.
-- source:
--   arXiv:1907.04383v3, Lemma 7, p. 11 (proof in Appendix A, pp. 13–15)

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Lemma 7, p. 11: for a promise template `(𝔸, 𝔹)`, BLP+Affine correctly solves
`PCSP-Decision(𝔸, 𝔹)` (Definition 1) iff `M_BLP+Aff` admits a minion homomorphism to
`Pol(𝔸, 𝔹)`. -/
theorem lemma_7 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹 ↔ HasMinionHomToPol 𝔸 𝔹 := by sorry

end PCSPBLPAff.Characterization
