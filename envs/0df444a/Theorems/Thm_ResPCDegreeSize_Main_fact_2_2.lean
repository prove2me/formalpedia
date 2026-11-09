-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_fact_2_2
-- name    : ResPCDegreeSize.Main.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:06.707362+00:00
-- url     : https://prove2.me/theorems/8714f0dc-3684-4bfa-bf8c-9bc1497af791
-- title:
--   Fact 2.2 — the multilinear representative
-- statement:
--   Every polynomial $f\in\mathbb F_p[x_1,\dots,x_n]$ has a unique multilinear polynomial $\mathrm{ML}(f)$ that agrees with $f$ on $\{0,1\}^n$. Moreover
--   $$\deg\mathrm{ML}(f)\le\deg f,\qquad \mathrm{Bool}\vdash_{\deg f}f-\mathrm{ML}(f).$$
--
--   So reduction to multilinear form costs no degree in polynomial calculus. The statement asserts multilinearity, agreement on the cube, uniqueness among multilinear polynomials, the degree bound and the derivation.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: the representative ML(f) is named by its uniqueness → ML is the explicit exponent-reducing map, and the statement proves it has the properties and is unique; reason: the representative is the same polynomial; an explicit definition avoids choosing it from the claim to be proved
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Fact 2.2, PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem fact_2_2 {n p : ℕ} [Fact p.Prime] (f : Poly n p) :
    IsMultilinear (ML f) ∧
    (∀ a : Fin n → Bool, eval (cubePoint p a) (ML f) = eval (cubePoint p a) f) ∧
    (∀ g : Poly n p, IsMultilinear g →
      (∀ a : Fin n → Bool, eval (cubePoint p a) g = eval (cubePoint p a) f) → g = ML f) ∧
    (ML f).totalDegree ≤ f.totalDegree ∧
    PCDerivable (boolAxioms n p) f.totalDegree (f - ML f) := by sorry

end ResPCDegreeSize.Main
