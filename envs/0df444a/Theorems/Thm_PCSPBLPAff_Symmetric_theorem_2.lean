-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_theorem_2
-- name    : PCSPBLPAff.Symmetric.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:17.023669+00:00
-- url     : https://prove2.me/theorems/a5d2f507-205c-4fec-969e-138e8bc7ff53
-- title:
--   Theorem 2, p. 6 — if Pol(A, B) has symmetric polymorphisms of arbitrarily large arities, BLP+Affine correctly solves PCSP-Decision(A, B)
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a promise template over finite domains $A$, $B$, i.e. relational structures of a common signature with a homomorphism $\mathbf A\to\mathbf B$. Suppose $\mathrm{Pol}(\mathbf A,\mathbf B)$ contains symmetric polymorphisms of arbitrarily large arities: for every $N\in\mathbb N$ there are $L\ge N$ and a symmetric polymorphism $f:A^L\to B$. Then
--   $$
--   \text{the BLP+Affine algorithm correctly solves } \mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B),
--   $$
--   that is, for every instance $X$: if $X$ is satisfiable in $\mathbf A$, the algorithm accepts $X$; and if the algorithm accepts $X$, then $X$ is satisfiable in $\mathbf B$.
--
--   The algorithm solves the Basic LP, takes a relative interior point, and checks whether the affine relaxation restricted to its support has an integer solution. The theorem shows that one algorithm covers every template with an infinite family of symmetric polymorphisms, without knowing the polymorphisms.
--
--   **Formalization Note** The algorithm is formalized by its acceptance condition (see the definitions module); polynomial running time is not part of the statement. The polymorphism hypothesis depends only on $(\mathbf A,\mathbf B)$ and precedes the quantifier over instances.
-- source:
--   arXiv:1907.04383v3, Theorem 2, p. 6

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Theorem 2 (arXiv:1907.04383v3, p. 6): if `Pol(𝔸, 𝔹)` has symmetric polymorphisms of
arbitrarily large arities, the BLP+Affine algorithm correctly solves `PCSP-Decision(𝔸, 𝔹)`. -/
theorem theorem_2 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (hT : IsPromiseTemplate 𝔸 𝔹)
    (hsym : ∀ N : ℕ, ∃ L : ℕ, N ≤ L ∧
      ∃ f : (Fin L → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f) :
    CorrectlySolves 𝔸 𝔹 := by sorry

end PCSPBLPAff.Symmetric
