-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_forgetting_potential
-- name    : RandomStreamCI.CodeIntersection.forgetting_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:39.919609+00:00
-- url     : https://prove2.me/theorems/c86769b1-4dd9-4c42-a39c-4864f2c0808e
-- title:
--   Lemma 15 — Forgetting cannot increase the potential
-- statement:
--   For every classical program and finite code, threshold $1\le\kappa\le n$, and $0<\eta<1/2$, the vertex and incoming-edge potentials satisfy
--
--   $$\forall t\in\{1,\ldots,M\},\quad\Phi_{\eta,\kappa}(t)\le\Psi_{\eta,\kappa}(t).$$
--
--   No injectivity or no-forgetting assumption is imposed on transitions. This isolates the contribution of state merging to the change in potential.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: threshold kappa in [n] and incoming edge time t in 1 through M → integer threshold with explicit bounds and Fin M indexing the edge arriving at time t.val + 1; reason: integer ceilings and real exponents avoid natural subtraction truncation and enumerate exactly the same times
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 15, printed p. 12 / PDF p. 12

import Definitions.Def_RandomStreamCI_CodeIntersection_Potential

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 15, p. 12 (37): all incoming layers, arbitrary forgetting. -/
theorem forgetting_potential {n w : ℕ} {Alphabet : Type} [Fintype Alphabet]
    [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (κ : ℤ) (hκ : 1 ≤ κ) (hκn : κ ≤ (n : ℤ))
    (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (t : Fin (Fintype.card (Address n Alphabet))) :
    vertexPotential B C η κ (t.val + 1) ≤ edgePotential B C η κ t := by sorry

end RandomStreamCI.CodeIntersection
