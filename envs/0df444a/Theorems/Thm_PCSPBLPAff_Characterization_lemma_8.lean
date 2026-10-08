-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_8
-- name    : PCSPBLPAff.Characterization.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:01.280989+00:00
-- url     : https://prove2.me/theorems/c936b924-2b8f-4adc-977d-309c6d848382
-- title:
--   Lemma 8, p. 11 — a minion homomorphism from M_BLP+Aff gives (2L+1)-ary polymorphisms with blocks of sizes L and L+1
-- statement:
--   Let $\mathbf A,\mathbf B$ be relational structures with the same signature. Suppose $\mathcal M_{\mathrm{BLP+Aff}}$ has a minion homomorphism to $\mathrm{Pol}(\mathbf A,\mathbf B)$. Then for every $L\in\mathbb N$ there is a polymorphism $f:A^{2L+1}\to B$ and a partition of $[2L+1]$ into two blocks, of sizes $L$ and $L+1$, such that $f$ is invariant under every permutation of its arguments that preserves both blocks:
--   $$\forall L\in\mathbb N\;\exists f\in\mathrm{Pol}^{(2L+1)}(\mathbf A,\mathbf B),\ [2L+1]=B_1\sqcup B_2,\ |B_1|=L,\ |B_2|=L+1,\ f\ \text{block-symmetric for}\ (B_1,B_2).$$
--
--   This is the direction "minion homomorphism ⇒ concrete polymorphisms" of the characterization in Theorem 4.
--
--   **Formalization Note** The partition is given by a labelling $\beta:[2L+1]\to\{0,1\}$; block $0$ has $L$ elements and block $1$ has $L+1$. As on the page, no promise-template hypothesis is assumed.
-- source:
--   arXiv:1907.04383v3, Lemma 8, p. 11

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Lemma 8, p. 11: if `M_BLP+Aff` has a minion homomorphism to `Pol(𝔸, 𝔹)`, then for every
`L ∈ ℕ`, `Pol(𝔸, 𝔹)` contains a block-symmetric polymorphism of arity `2L + 1` with two blocks
of size `L` and `L + 1`. -/
theorem lemma_8 {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (h : HasMinionHomToPol 𝔸 𝔹) :
    ∀ L : ℕ, ∃ f : (Fin (2 * L + 1) → A) → B, PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧
      ∃ β : Fin (2 * L + 1) → Fin 2,
        (Finset.univ.filter (fun l => β l = 0)).card = L ∧
        (Finset.univ.filter (fun l => β l = 1)).card = L + 1 ∧
        PCSPBLPAff.Symmetric.IsBlockSymmetricFor β f := by sorry

end PCSPBLPAff.Characterization
