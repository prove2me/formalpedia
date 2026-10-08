-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_example_10
-- name    : PCSPBLPAff.Characterization.example_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:01.664364+00:00
-- url     : https://prove2.me/theorems/d064b9f6-ce8e-4fc9-815b-4f3996beb36c
-- title:
--   Example 10, p. 13 — the union of a directed 2-cycle and 3-cycle has no block-symmetric polymorphism of width greater than one
-- statement:
--   Let $\mathbf A$ be the digraph on $\{0,1\}\sqcup\{0',1',2'\}$ that is the disjoint union of the directed 2-cycle $0\to1\to0$ and the directed 3-cycle $0'\to1'\to2'\to0'$. Then no polymorphism $f\in\mathrm{Pol}(\mathbf A,\mathbf A)$, of any arity, is block-symmetric of width at least $2$:
--   $$\forall L\ \forall f:A^L\to A\ \text{polymorphism}:\quad \neg\,(\text{width}(f)\ge2).$$
--
--   By Theorem 4, the BLP+Affine algorithm therefore does not solve $\mathrm{PCSP}(\mathbf A,\mathbf A)$, although this template is tractable; the condition of Theorem 4 is not preserved under disjoint union.
--
--   **Formalization Note** Only the claim proved on the page is formalized. The statements that $\mathrm{PCSP}(\mathbf A,\mathbf A)$ is solvable in polynomial time and that $\mathrm{Pol}(\mathbf A,\mathbf A)$ has cyclic polymorphisms of every prime arity $p>3$ are not part of this item.
-- source:
--   arXiv:1907.04383v3, Example 10 and its proof, p. 13

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Example 10, p. 13 (the claim proved there): the disjoint union of a directed 2-cycle and a
directed 3-cycle has no block-symmetric polymorphism `f ∈ Pol(A, A)` of width greater than one. -/
theorem example_10 :
    ∀ (L : ℕ) (f : (Fin L → Fin 2 ⊕ Fin 3) → Fin 2 ⊕ Fin 3),
      PCSPBLPAff.Symmetric.IsPolymorphism example10Digraph example10Digraph f → ¬ PCSPBLPAff.Symmetric.HasWidthAtLeast f 2 := by sorry

end PCSPBLPAff.Characterization
