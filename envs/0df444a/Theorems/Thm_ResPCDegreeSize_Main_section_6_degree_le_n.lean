-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_section_6_degree_le_n
-- name    : ResPCDegreeSize.Main.section_6_degree_le_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:46.041196+00:00
-- url     : https://prove2.me/theorems/e983a877-5829-4d87-a7d7-3b2aa1ed6a22
-- title:
--   Section 6, first paragraph — PC refutes $\mathcal Q(F)$ in degree $n$ for CNFs and $n+1$ for the systems of Remark 1.2, hence $D\le n$
-- statement:
--   For an unsatisfiable CNF $F$ on $n$ variables, polynomial calculus refutes $\mathcal Q(F)$ in degree $n$:
--   $$\mathcal Q(F)\vdash_n1.$$
--   For an unsatisfiable polynomial equation system $F=\{F_1,\dots,F_m\}$ as in Remark 1.2, with $F_i=\bigvee_{j=1}^{w_i}(H_{i,j}=0)$, $\deg H_{i,j}\le r$, and encoding
--   $$\mathcal Q(F)=\mathrm{Bool}\cup\{Q_{F_1},\dots,Q_{F_m}\},\qquad Q_{F_i}=\mathrm{ML}\Bigl(\prod_{j=1}^{w_i}H_{i,j}\Bigr),$$
--   polynomial calculus refutes $\mathcal Q(F)$ in degree $n+1$:
--   $$\mathcal Q(F)\vdash_{n+1}1.$$
--   Consequently, in both cases, $\mathcal Q(F)\nvdash_D1$ implies $D\le n$.
--
--   The hypothesis of the main theorem therefore bounds $D$ by the number of variables, which the parameter computation of Section 6 needs.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: variables x_1,…,x_n; a clause is a set of literals → variables indexed by Fin n; Literal is a variable with a sign, and a clause is a Finset of literals; reason: relabelling only; the literal polynomials are x_i and 1 − x_i as in the source
--   - encoding: F_p → ZMod p with [Fact p.Prime]; reason: ZMod p is the field with p elements
--   - encoding: the system F = {F_1,…,F_m}, F_i = ⋁_{j=1}^{w_i}(H_{i,j} = 0), of Remark 1.2 and its encoding (3) → w : Fin m → ℕ, H : ∀ i, Fin (w i) → Poly n p, and polyEncoding H; reason: the same indexing as the remark; polyEncoding H is Bool ∪ {ML(∏_j H_{i,j})}
--   - reading: "in degree n + 1 for multilinear polynomials as in Remark 1.2", without repeating "unsatisfiable" → PolyUnsatisfiable H is a hypothesis of that clause; reason: a system with a solution on the cube has no refutation at all, so the sentence can only mean unsatisfiable systems, as in its CNF half
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 6, first paragraph and footnote 4, PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem section_6_degree_le_n {n p : ℕ} [Fact p.Prime] :
    (∀ F : CNF n, Unsatisfiable F →
      (1 : Poly n p) ∈ CD (encoding p F) n ∧
      ∀ D : ℕ, (1 : Poly n p) ∉ CD (encoding p F) D → D ≤ n) ∧
    (∀ (r m : ℕ) (w : Fin m → ℕ) (H : ∀ i, Fin (w i) → Poly n p),
      (∀ i j, (H i j).totalDegree ≤ r) → PolyUnsatisfiable H →
      (1 : Poly n p) ∈ CD (polyEncoding H) (n + 1) ∧
      ∀ D : ℕ, (1 : Poly n p) ∉ CD (polyEncoding H) D → D ≤ n) := by sorry

end ResPCDegreeSize.Main
