-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_11_2_1
-- name    : WildeQIT.Compression.Supplement.theorem_11_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:13:07.284718+00:00
-- url     : https://prove2.me/theorems/995cd737-3840-59df-99fc-61e2e144dfc1
-- title:
--   Theorem 11.2.1: $H(A)_\varphi=H(B)_\varphi$ and $H(AB)_\varphi=0$ for a pure bipartite state
-- statement:
--   Let $|\varphi\rangle_{AB}$ be a pure state of a bipartite system $AB$, with marginals $\varphi_A=\operatorname{Tr}_B\{|\varphi\rangle\langle\varphi|\}$ and $\varphi_B=\operatorname{Tr}_A\{|\varphi\rangle\langle\varphi|\}$, and let $H$ denote the quantum (von Neumann) entropy in bits. Then
--
--   1. the marginal entropies are equal: $H(A)_\varphi=H(B)_\varphi$;
--   2. the joint entropy vanishes: $H(AB)_\varphi=0$.
--
--   The first statement is a consequence of the Schmidt decomposition; together they show that the entropy of a marginal of a pure state measures its entanglement.
--
--   **Formalization Note** $|\varphi\rangle$ is a unit vector on the product index type $a\times b$ and $H$ is the published `WildeQIT.QMemory.vonNeumann`.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.2.1, p. 325, eqs. (11.23)–(11.24)

import Mathlib
import Definitions.Def_WildeQIT_QMemory_vonNeumann
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.2.1, p. 325.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 11.2.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 325): "The marginal entropies `H(A)_φ` and `H(B)_φ` of a
pure bipartite state `|φ⟩_AB` are equal: `H(A)_φ = H(B)_φ` (11.23), while the joint entropy
`H(AB)_φ` vanishes: `H(AB)_φ = 0` (11.24)."

Formalization Note: `|φ⟩_AB` is a unit vector on `a × b`, its density operator `|φ⟩⟨φ|` the
published `QAlgorithms.pureDensity`; `φ_A = Tr_B` and `φ_B = Tr_A` are the published partial
traces; `H` is the published quantum entropy `WildeQIT.QMemory.vonNeumann` (bits). -/
theorem theorem_11_2_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (φ : EuclideanSpace ℂ (a × b)) (hφ : ‖φ‖ = 1) :
    WildeQIT.QMemory.vonNeumann (WildeQIT.partialTraceRight (QAlgorithms.pureDensity φ)) =
        WildeQIT.QMemory.vonNeumann (WildeQIT.partialTraceLeft (QAlgorithms.pureDensity φ)) ∧
      WildeQIT.QMemory.vonNeumann (QAlgorithms.pureDensity φ) = 0 := by sorry

end WildeQIT.Compression.Supplement
