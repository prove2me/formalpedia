-- Prove2me | Theorems.Thm_PsdPermanent_lemma_8
-- name    : PsdPermanent.lemma_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:31:31.931306+00:00
-- url     : https://prove2.me/theorems/acb362ec-3080-4efd-898b-d6b2bdffbdf2
-- title:
--   Lemma 8 — trace normalization at the optimum
-- statement:
--   Let $V\in\mathbb C^{n\times d}$ have full column rank and nonzero rows, and let $X_\star\succ0$ maximize $\phi_V$ over the Hermitian positive definite matrices. Then
--   $$\operatorname{tr}X_\star=n+d.$$
--
--   This places the optimizer in a known compact convex set.
--
--   Differences from the source:
--   - encoding: v_i†Xv_i, det X, trX → real parts of (V X V†)_ii, det X, trace X; reason: all three are real on positive definite X
--   - generalization: H_d^{++} defined for d ≥ 1 (§3) → d = 0 allowed, the empty matrix being positive definite with det = 1; reason: the d ≥ 1 statements are a special case; d = 0 is the one-point space (and forces n = 0 where rows are nonzero)
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 8, p.8

import Mathlib
import Definitions.Def_PsdPermanent_phi
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Lemma 8 (Trace normalization at the optimum).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 8, p.8: "Let X⋆ maximize ϕ_V. Then trX⋆ = n + d."

**Formalization Note.** §4's standing hypotheses on `V`: full column rank and nonzero rows. A maximizer is a positive
definite `X` with `phi V Y ≤ phi V X` for every positive definite `Y`. -/
theorem lemma_8 {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hrank : V.rank = d) (hV : ∀ i, V i ≠ 0)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef) (hmax : ∀ Y : Matrix (Fin d) (Fin d) ℂ, Y.PosDef → phi V Y ≤ phi V X) :
    X.trace = (n : ℂ) + d := by sorry

end PsdPermanent
