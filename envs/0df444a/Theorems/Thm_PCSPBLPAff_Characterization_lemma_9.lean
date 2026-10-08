-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_9
-- name    : PCSPBLPAff.Characterization.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:39.284212+00:00
-- url     : https://prove2.me/theorems/b9e5a3c3-a09b-4fe2-bec8-65f4c3ad1463
-- title:
--   Lemma 9, p. 11 — block-symmetric polymorphisms of arbitrarily high width give a minion homomorphism from M_BLP+Aff
-- statement:
--   Let $\mathbf A,\mathbf B$ be relational structures with the same signature on finite domains $A,B$. Suppose that for every $N\in\mathbb N$ there is a polymorphism $f\in\mathrm{Pol}(\mathbf A,\mathbf B)$ that is block-symmetric of width at least $N$, i.e. for some partition of its coordinates into at least one block, every block has at least $N$ elements and $f$ is invariant under permutations within each block. Then
--   $$\mathcal M_{\mathrm{BLP+Aff}}\ \text{admits a minion homomorphism to}\ \mathrm{Pol}(\mathbf A,\mathbf B).$$
--
--   This is the direction "concrete polymorphisms ⇒ minion homomorphism" of Theorem 4; together with Lemmas 7 and 8 it closes the cycle of equivalences.
--
--   **Formalization Note** The statement is the many-block version asserted by the lemma, not only the one-block case treated in the paper's proof. No promise-template hypothesis is assumed, as on the page.
-- source:
--   arXiv:1907.04383v3, Lemma 9, p. 11

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Lemma 9, p. 11: if `Pol(𝔸, 𝔹)` (for `A`, `B` finite) contains block-symmetric
polymorphisms of arbitrarily high width, then `M_BLP+Aff` admits a minion homomorphism to
`Pol(𝔸, 𝔹)`. -/
theorem lemma_9 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (h : ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B),
      PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧ PCSPBLPAff.Symmetric.HasWidthAtLeast f N) :
    HasMinionHomToPol 𝔸 𝔹 := by sorry

end PCSPBLPAff.Characterization
