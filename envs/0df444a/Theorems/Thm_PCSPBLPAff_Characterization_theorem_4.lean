-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_theorem_4
-- name    : PCSPBLPAff.Characterization.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:54.363985+00:00
-- url     : https://prove2.me/theorems/b7db34a7-4e49-4acb-90b5-a086cc7210a9
-- title:
--   Theorem 4, p. 9 — BLP+Affine solves PCSP(A, B) iff Pol(A, B) has block-symmetric polymorphisms of arbitrarily high width iff (2L+1)-ary ones with blocks L, L+1
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a promise template on finite domains $A$, $B$. The following are equivalent:
--
--   1. the BLP+Affine algorithm correctly solves $\mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B)$, i.e. it accepts every instance satisfiable in $\mathbf A$ and rejects every instance unsatisfiable in $\mathbf B$;
--   2. $\mathrm{Pol}(\mathbf A,\mathbf B)$ has block-symmetric polymorphisms of arbitrarily high width: for every $N\in\mathbb N$ some polymorphism $f$ is invariant under permutations within each block of a partition of its coordinates into at least one block, every block having at least $N$ elements;
--   3. for every $L\in\mathbb N$, $\mathrm{Pol}(\mathbf A,\mathbf B)$ has a block-symmetric polymorphism of arity $2L+1$ with two symmetric blocks of variables of sizes $L$ and $L+1$.
--
--   $$\text{BLP+Affine solves }\mathrm{PCSP}(\mathbf A,\mathbf B)\iff \sup_{f\in\mathrm{Pol}(\mathbf A,\mathbf B)}\mathrm{width}(f)=\infty\iff \forall L\ \exists f\in\mathrm{Pol}^{(2L+1)}\ \text{symmetric on blocks of sizes }L,\,L+1.$$
--
--   This is the paper's exact characterization of the power of the combined Basic LP and affine relaxation for promise CSPs.
--
--   **Formalization Note** The algorithm is formalized through its acceptance condition (see the definitions file); the polynomial-time claims are not formalized. In item 3 the two blocks are given by a labelling $\beta:[2L+1]\to\{0,1\}$ with $|\beta^{-1}(0)|=L$ and $|\beta^{-1}(1)|=L+1$.
-- source:
--   arXiv:1907.04383v3, Theorem 4, p. 9

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Theorem 4, p. 9: for a promise template `(𝔸, 𝔹)` the following are equivalent:
(1) the BLP+Affine algorithm correctly solves `PCSP-Decision(𝔸, 𝔹)`;
(2) `Pol(𝔸, 𝔹)` has block-symmetric polymorphisms of arbitrarily high width;
(3) for every `L ∈ ℕ`, `Pol(𝔸, 𝔹)` has a block-symmetric polymorphism of arity `2L + 1` with
two symmetric blocks of variables of size `L` and `L + 1`. -/
theorem theorem_4 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    List.TFAE
      [ PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹,
        ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B), PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧ PCSPBLPAff.Symmetric.HasWidthAtLeast f N,
        ∀ L : ℕ, ∃ f : (Fin (2 * L + 1) → A) → B, PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧
          ∃ β : Fin (2 * L + 1) → Fin 2,
            (Finset.univ.filter (fun l => β l = 0)).card = L ∧
            (Finset.univ.filter (fun l => β l = 1)).card = L + 1 ∧
            PCSPBLPAff.Symmetric.IsBlockSymmetricFor β f ] := by sorry

end PCSPBLPAff.Characterization
