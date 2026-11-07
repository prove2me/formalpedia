-- Prove2me | Theorems.Thm_PsdPermanent_phi_concaveOn
-- name    : PsdPermanent.phi_concaveOn
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:36.10799+00:00
-- url     : https://prove2.me/theorems/22fe044e-2a78-4dc1-bc8e-694a5643d3b2
-- title:
--   §4, p.5 — $\phi_V$ is concave on $\mathbb H_d^{++}$
-- statement:
--   Let $V\in\mathbb C^{n\times d}$ have nonzero rows. The function $\phi_V$ is concave on the Hermitian positive definite $d\times d$ matrices.
--
--   This is what places the relaxation within convex optimization.
--
--   Differences from the source:
--   - encoding: v_i†Xv_i, det X, trX → real parts of (V X V†)_ii, det X, trace X; reason: all three are real on positive definite X
--   - generalization: §4's standing hypothesis that V is a full column rank factor of A = V V† of rank d → any V with nonzero rows; reason: concavity uses only v_i ≠ 0 (each X ↦ v_i†Xv_i is then a positive linear functional on positive definite X); full column rank factors are a special case
--   - generalization: H_d^{++} defined for d ≥ 1 (§3) → d = 0 allowed, the empty matrix being positive definite with det = 1; reason: the d ≥ 1 statements are a special case; d = 0 is the one-point space (and forces n = 0 where rows are nonzero)
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §4, p.5

import Mathlib
import Definitions.Def_PsdPermanent_phi
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **ϕ_V is concave.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §4, p.5: "The objective is concave on H_d^{++}: each X ↦ log(v_i† X v_i) is the logarithm of a positive linear
functional, log det X is concave, and −trX is linear."

**Formalization Note.** §4's nonzero rows. `ConcaveOn` also asserts that the positive definite matrices are a
convex subset of the complex matrices, viewed as a real vector space. -/
theorem phi_concaveOn {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hV : ∀ i, V i ≠ 0) :
    ConcaveOn ℝ {X : Matrix (Fin d) (Fin d) ℂ | X.PosDef} (phi V) := by sorry

end PsdPermanent
