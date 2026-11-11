-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_potential_bounds_success
-- name    : RandomStreamCI.CodeIntersection.potential_bounds_success
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:27.393834+00:00
-- url     : https://prove2.me/theorems/46e6c8c9-170e-41da-a3ab-19cc22b49382
-- title:
--   Lemma 14 — Initial potential and full terminal success bound
-- statement:
--   Let $B$ be any classical program for a finite Code Intersection instance. For every threshold $1\le\kappa\le n$ and $0<\eta<1/2$, its threshold crossing potential satisfies both
--
--   $$\Phi_{\eta,\kappa}(0)=0,\qquad \Pr[B\text{ succeeds}]\le2\eta+\Phi_{\eta,\kappa}(M).$$
--
--   The terminal success is computed from the program's actual output and original uniform oracle/order law. This connects the potential to the search relation rather than to the expected number of solutions.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: threshold kappa in [n] and incoming edge time t in 1 through M → integer threshold with explicit bounds and Fin M indexing the edge arriving at time t.val + 1; reason: integer ceilings and real exponents avoid natural subtraction truncation and enumerate exactly the same times
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 14, printed p. 11 / PDF p. 11

import Definitions.Def_RandomStreamCI_CodeIntersection_Potential

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 14, p. 11 (30), both initial and terminal assertions. -/
theorem potential_bounds_success {n w : ℕ} {Alphabet : Type} [Fintype Alphabet]
    [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (κ : ℤ) (hκ : 1 ≤ κ) (hκn : κ ≤ (n : ℤ))
    (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) :
    vertexPotential B C η κ 0 = 0 ∧
      B.success C ≤ 2 * η + vertexPotential B C η κ (Fintype.card (Address n Alphabet)) := by sorry

end RandomStreamCI.CodeIntersection
