-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_observation_15
-- name    : PCSPBLPAff.Characterization.observation_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:39.95398+00:00
-- url     : https://prove2.me/theorems/2806d9f4-d0b9-480e-af77-38703120360e
-- title:
--   Observation 15, pp. 14–15 — BLP+Affine correctly solves PCSP(A, B) iff X → F_{M_BLP+Aff}(A) implies X → B
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a promise template on finite domains. The following are equivalent:
--
--   1. the BLP+Affine algorithm correctly solves $\mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B)$;
--   2. for every instance $X$, if $X$ is satisfiable in the free structure $F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)$ then $X$ is satisfiable in $\mathbf B$:
--   $$\forall X:\quad X\to F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)\ \Longrightarrow\ X\to\mathbf B.$$
--
--   This restates Definition 1 through the free structure; it is the first step of the proof of Lemma 7 in Appendix A.
-- source:
--   arXiv:1907.04383v3, Observation 15, pp. 14–15

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Observation 15, pp. 14–15: for a promise template `(𝔸, 𝔹)`, BLP+Affine correctly solves
`PCSP-Decision(𝔸, 𝔹)` iff every instance satisfiable in the free structure
`F_{M_BLP+Aff}(𝔸)` is satisfiable in `𝔹`. -/
theorem observation_15 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹 ↔ ∀ X : PCSPBLPAff.Symmetric.Instance τ ar, PCSPBLPAff.Symmetric.SatIn X (freeStruct 𝔸) → PCSPBLPAff.Symmetric.SatIn X 𝔹 := by sorry

end PCSPBLPAff.Characterization
