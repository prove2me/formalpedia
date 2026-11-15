-- Prove2me | Theorems.Thm_ResultantVNP_circuit_substitution_bound
-- name    : ResultantVNP.circuit_substitution_bound
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T09:00:48.737322+00:00
-- url     : https://prove2.me/theorems/f6f4c884-2775-4a5f-b115-e4f071846199
-- title:
--   Arithmetic-circuit substitution with a gate-count bound
-- statement:
--   Let C be a fan-in-two arithmetic circuit over $\mathbb C$ with variables in an arbitrary type $\sigma$, and let $g$ be its number of addition and multiplication gates. Let $f_x$ be a polynomial in variables of type $\tau$ for every $x\in\sigma$. Suppose each $f_x$ has an arithmetic circuit with at most $s$ gates. Then the polynomial obtained by substituting $x\mapsto f_x$ in the output of C has a circuit D satisfying
--
--   $$D(\mathbf y)=C((f_x(\mathbf y))_{x\in\sigma}),\qquad \operatorname{size}(D)\le (2g+1)(s+1).$$
--
--   Size counts gates only. The assertion imposes no bound on the number of leaf nodes in C and allows repeated variables, arbitrary complex constants, and shared intermediate results. This is a reusable composition estimate for the ResultantVNP.Circuit representation.
-- source:
--   Supporting circuit-composition claim for Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission #1103, Section 3.1 circuit convention, p.14. The explicit bound is a derived auxiliary claim, not a separately numbered statement in the paper. It follows by pruning unused nodes, using at most 2g+1 input leaves, and grafting the substitution circuits. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1103.pdf

import Mathlib
import Definitions.Def_ResultantVNP_Circuit

namespace ResultantVNP

theorem circuit_substitution_bound {σ τ : Type} (C : Circuit σ)
    (f : σ → MvPolynomial τ ℂ) (s : ℕ)
    (hf : ∀ x, ∃ D : Circuit τ, D.value = f x ∧ D.size ≤ s) :
    ∃ D : Circuit τ,
      D.value = MvPolynomial.aeval f C.value ∧
      D.size ≤ (2 * C.size + 1) * (s + 1) := by
  sorry

end ResultantVNP
