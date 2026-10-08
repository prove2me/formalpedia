-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_16
-- name    : PCSPBLPAff.Characterization.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:50.864991+00:00
-- url     : https://prove2.me/theorems/e24ff677-1e60-4ccf-88fd-2bb0408a544b
-- title:
--   Lemma 16 (compactness for structures), p. 15 — if every finite induced substructure of F maps to a finite B, so does F
-- statement:
--   Let $\mathbf F$ and $\mathbf B$ be relational structures with the same signature, on domains $D$ and $B$, with $B$ finite. Suppose that for every finite subset $S\subseteq D$, the substructure of $\mathbf F$ induced on $S$ admits a homomorphism to $\mathbf B$. Then $\mathbf F$ admits a homomorphism to $\mathbf B$:
--   $$\bigl(\forall S\subseteq D\ \text{finite}:\ \mathbf F[S]\to\mathbf B\bigr)\ \Longrightarrow\ \mathbf F\to\mathbf B.$$
--
--   This generalization of the de Bruijn–Erdős theorem turns the instance-wise condition of Observation 15 into the single homomorphism $F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)\to\mathbf B$.
--
--   **Formalization Note** A homomorphism from $\mathbf F[S]$ is encoded as a map $D\to B$ that is required to preserve only the tuples of $\mathbf F$ with all entries in $S$; its values off $S$ are irrelevant. The page's hypothesis that $\mathbf F$ is infinite is dropped: for finite $\mathbf F$ the statement is immediate (take $S=D$), and the generalization lets the lemma apply to every free structure, including the empty one.
-- source:
--   arXiv:1907.04383v3, Lemma 16, p. 15

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Lemma 16 (compactness for structures), p. 15: if `𝔹` is finite and every finite induced
substructure of `𝔽` admits a homomorphism to `𝔹`, then so does `𝔽`. A homomorphism from the
substructure induced on a finite set `S` is encoded as a map `D → B` that is checked only on
the tuples with all entries in `S`. -/
theorem lemma_16 {τ : Type} {ar : τ → ℕ} {D B : Type} [Finite B]
    (𝔽 : PCSPBLPAff.Symmetric.RelStruct τ ar D) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (h : ∀ S : Finset D, ∃ σ : D → B,
      ∀ R : τ, ∀ t ∈ 𝔽.rel R, (∀ k, t k ∈ S) → σ ∘ t ∈ 𝔹.rel R) :
    ∃ σ : D → B, PCSPBLPAff.Symmetric.IsHom 𝔽 𝔹 σ := by sorry

end PCSPBLPAff.Characterization
