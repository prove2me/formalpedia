-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_4_6
-- name    : ResultantVNP.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:00:33.504203+00:00
-- url     : https://prove2.me/theorems/b4a3d064-1039-452a-82e4-c0563b691258
-- title:
--   Theorem 4.6 — $\mathrm{Det}_n(A)\bmod 2^k$ is $\mathsf{FP}^{\mathsf{PP}}$-complete under Turing reductions
-- statement:
--   For explicitly encoded integer symmetric cubic tensors $A$ and $k\ge1$ supplied in unary, computing
--   $$\mathrm{Det}_n(A)\bmod 2^k\in\{0,\dots,2^k-1\}$$
--   is **$\mathsf{FP}^{\mathsf{PP}}$-complete under polynomial-time Turing reductions**:
--
--   1. the function $\mathrm{DetMod}$ lies in $\mathsf{FP}^{\mathsf{PP}}$, and
--   2. every function in $\mathsf{FP}^{\mathsf{PP}}$ is computable in polynomial time with an oracle for $\mathrm{DetMod}$.
--
--   The upper bound matches the lower bound of Theorem 1.8, which settles the complexity of dyadic modular evaluation of symmetric tensor determinants.
--
--   **Formalization Note** An oracle for $\mathrm{DetMod}$ is its bit graph. The resultant comes from an arbitrary resultant system.
--
--   Differences from the source:
--   - reading: "$k\ge1$ is supplied in unary, or equivalently the modulus $2^k$ is supplied in ordinary binary notation" → $k$ in unary only; reason: the clause asserts that the two input formats are interchangeable (both have length about $k$), not a separate result.
--   - encoding: an oracle for the function $\mathrm{DetMod}$ → an oracle for its bit graph; reason: oracle machines query languages; for outputs of polynomial length (at most $k$ bits) the two are equivalent.
--   - encoding: "the resultant" → an arbitrary `ResultantSystem`; reason: all resultant systems agree with the unique resultant of Definition 2.1 for $n\ge1$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 4.6, p.21

import Mathlib
import Definitions.Def_ResultantVNP_Supplement_SymTensor

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

/-- **Theorem 4.6 (Dyadic modular evaluation).** For explicitly encoded integer symmetric cubic
tensors `A`, computing `Det_n(A) mod 2^k` is FP^PP-complete under polynomial-time Turing
reductions. Here `k ≥ 1` is supplied in unary.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 4.6, p.21 (proof p.21 and Lemma B.2, p.39).

**Formalization Note** Membership: `DetMod 𝓡 ∈ FP^A` for some `A ∈ PP`. Hardness: every
`f ∈ FP^PP` is computed in polynomial time with an oracle for `DetMod 𝓡` (its bit graph
`outputGraph`). The remark "or equivalently the modulus `2^k` is supplied in ordinary binary
notation" is about the input format and is not stated separately. The resultant is taken from an
arbitrary `ResultantSystem` `𝓡`. -/
theorem theorem_4_6 (𝓡 : ResultantSystem) :
    DetMod 𝓡 ∈ FPPP ∧ ∀ f ∈ FPPP, TuringReducesTo f (DetMod 𝓡) := by sorry

end Supplement

end ResultantVNP
