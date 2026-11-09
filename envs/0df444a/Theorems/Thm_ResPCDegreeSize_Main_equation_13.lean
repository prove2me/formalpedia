-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_equation_13
-- name    : ResPCDegreeSize.Main.equation_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:38.87887+00:00
-- url     : https://prove2.me/theorems/1c7204b7-cd85-4355-a9e6-376b92cd7619
-- title:
--   Section 2, eq. (13) — Fermat on the Boolean cube
-- statement:
--   For $g\in\mathbb F_p[x]$ with $\deg g\le d$,
--   $$\mathrm{Bool}\vdash_{pd}g^p-g.$$
--
--   This low-degree form of Fermat's little theorem is the only place the characteristic enters the multiplication maps.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 2, eq. (13), PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem equation_13 {n p d : ℕ} [Fact p.Prime] (g : Poly n p) (hg : g.totalDegree ≤ d) :
    PCDerivable (boolAxioms n p) (p * d) (g ^ p - g) := by sorry

end ResPCDegreeSize.Main
