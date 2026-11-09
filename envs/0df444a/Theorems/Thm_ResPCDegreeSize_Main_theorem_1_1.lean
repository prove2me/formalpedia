-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_theorem_1_1
-- name    : ResPCDegreeSize.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:33.913297+00:00
-- url     : https://prove2.me/theorems/07a248b3-ad25-4d57-8dcd-629c15661251
-- title:
--   Theorem 1.1 — degree–size relation for $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$
-- statement:
--   Let $p$ be a prime, $r\ge1$, and $F$ an unsatisfiable CNF of width $w(F)$ on $n$ Boolean variables. Suppose $\mathcal Q(F)\nvdash_D1$ in polynomial calculus over $\mathbb F_p$, where
--   $$D\ge\max\{32(p-1)^2r,\ 8w(F)\}.$$
--   Then every $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$ refutation of $F$ with $S$ nodes satisfies
--   $$\ln S\ge\frac{D}{32p^2r}\Bigl(\frac{D}{16n}\Bigr)^{(p-1)r}.\tag{2}$$
--
--   The logarithm is natural, and refutations are arbitrary DAGs. For constant $p,r,w(F)$, a linear polynomial calculus degree lower bound therefore gives an exponential size lower bound.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - generalization: a Res(PC_r/F_p) refutation is a finite DAG of disjunctions, with weakening, contraction, deletion of false constants, linear combination and multiplication, and S counts its nodes → lines are Finsets of polynomials of degree at most r (contraction and reordering are built in, weakening is ⊆), a refutation is a list whose entries follow from earlier entries and whose last entry is empty, unreachable entries are allowed, and S is the list length; reason: each paper refutation maps node by node to a list refutation with at most as many entries, so the Lean statement covers every paper refutation; the multiplier g of the multiplication rule carries no separate degree bound because deg(fg) ≤ r bounds it when f ≠ 0 and the line is unchanged when f = 0
--   - encoding: variables x_1,…,x_n; a clause is a set of literals → variables indexed by Fin n; Literal is a variable with a sign, and a clause is a Finset of literals; reason: relabelling only; the literal polynomials are x_i and 1 − x_i as in the source
--   - encoding: F_p → ZMod p with [Fact p.Prime]; reason: ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Theorem 1.1, eq. (2), PDF p. 2 (printed p. 1); proof Section 6, PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_ResolutionOverPolynomials
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem theorem_1_1 {n p r D : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    (F : CNF n) (hF : Unsatisfiable F)
    (hD : max (32 * (p - 1) ^ 2 * r) (8 * width F) ≤ D)
    (h1 : (1 : Poly n p) ∉ CD (encoding p F) D)
    (R : ResRefutation p F r) :
    (D : ℝ) / (32 * (p : ℝ) ^ 2 * r) * ((D : ℝ) / (16 * n)) ^ ((p - 1) * r) ≤
      Real.log (R.size : ℝ) := by sorry

end ResPCDegreeSize.Main
