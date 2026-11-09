-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_fact_2_1
-- name    : ResPCDegreeSize.Main.fact_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:35.940195+00:00
-- url     : https://prove2.me/theorems/c3c866ca-59bf-4cb3-b671-5c6d75680acb
-- title:
--   Fact 2.1 — degree-bounded multiplication in polynomial calculus
-- statement:
--   Let $A$ be a set of polynomials in $\mathbb F_p[x_1,\dots,x_n]$. If $A\vdash_D f$, then for every polynomial $g$,
--   $$A\vdash_{\max\{D,\deg f+\deg g\}}fg.$$
--   Consequently, for $\mathcal C_D=\mathcal C_D(A)$,
--   $$f\in\mathcal C_D,\quad \deg f+\deg g\le D\quad\Longrightarrow\quad fg\in\mathcal C_D.$$
--
--   This absorption property is what replaces ideal membership in every later degree count.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Fact 2.1, eq. (12), PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem fact_2_1 {n p : ℕ} [Fact p.Prime] (A : Set (Poly n p)) (D : ℕ) :
    (∀ f g : Poly n p, PCDerivable A D f →
      PCDerivable A (max D (f.totalDegree + g.totalDegree)) (f * g)) ∧
    (∀ f g : Poly n p, f ∈ CD A D → f.totalDegree + g.totalDegree ≤ D → f * g ∈ CD A D) := by sorry

end ResPCDegreeSize.Main
