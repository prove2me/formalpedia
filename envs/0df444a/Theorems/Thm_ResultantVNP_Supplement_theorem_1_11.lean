-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_1_11
-- name    : ResultantVNP.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:59:08.464745+00:00
-- url     : https://prove2.me/theorems/2b0aa023-f57d-4cf3-a60c-f4145a3609d8
-- title:
--   Theorem 1.11 — deciding $\mathrm{Res}^{(2)}_n>0$ is $\oplus$P-hard, already for sparse symmetric tensor determinants
-- statement:
--   1. Given quadratic forms $f_1,\dots,f_n\in\mathbb Z[x]$, deciding whether
--   $$\mathrm{Res}^{(2)}_n(f_1,\dots,f_n)>0$$
--   is $\oplus\mathsf P$-hard under polynomial-time many-one reductions.
--   2. The hardness already holds for deciding whether $\mathrm{Det}_n(A)>0$, where $A$ is an integer symmetric cubic tensor of dimension $n$ with $O(n)$ nonzero entries and $\mathrm{Det}_n(A)\ne0$. Precisely: there is one constant $c$ such that every $\oplus\mathsf P$ language $L$ has a polynomial-time map sending each $x$ to an integer symmetric tensor $A$ of some dimension $n\ge1$ with at most $c\,n$ nonzero entries and $\mathrm{Det}_n(A)\ne0$, such that $x\in L$ exactly when $\mathrm{Det}_n(A)>0$.
--
--   So even the sign of the resultant of integer quadratic forms is hard to compute. If it were in the polynomial hierarchy, the hierarchy would collapse.
--
--   **Formalization Note** Nonzero entries are counted in the $n\times n\times n$ array. The resultant comes from an arbitrary resultant system.
--
--   Differences from the source:
--   - reading: "with $O(n)$ nonzero entries and $\mathrm{Det}_n(A)\ne0$" → one constant $c$, fixed before the language, bounds the nonzero entries by $c\,n$ on every output of the reduction, and every output has $\mathrm{Det}_n(A)\ne0$; reason: the standard meaning of a promise and of a uniform $O(n)$ bound on the hard instances.
--   - encoding: instances → fixed injective binary codes, valid only for $n\ge1$; reason: decision problems on words; valid inputs are unchanged.
--   - encoding: "the resultant" → an arbitrary `ResultantSystem`; reason: all resultant systems agree with the unique resultant of Definition 2.1 for $n\ge1$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.11, p.7

import Mathlib
import Definitions.Def_ResultantVNP_Supplement_QuadSystem
import Definitions.Def_ResultantVNP_Supplement_SymTensor

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Theorem 1.11 (Hardness of sign computation).** Given quadratic forms `f₁, …, fₙ ∈ ℤ[x]`,
deciding whether `Res^{(2)}_n(f₁, …, fₙ) > 0` is ⊕P-hard under polynomial time many-one
reductions. The hardness in fact holds for deciding whether `Det_n(A) > 0`, where `A` is an integer
symmetric cubic tensor of dimension `n` with `O(n)` nonzero entries and `Det_n(A) ≠ 0`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.11, p.7 (proof pp.22–23).

**Formalization Note** (1): every ⊕P language many-one reduces to `ResPos 𝓡`. (2): one constant
`c` (chosen before the language) such that every ⊕P language `L` has a polynomial-time `u` mapping
each `x` to the code of a symmetric integer tensor of some dimension `n ≥ 1` with at most `c·n`
nonzero entries of its `n × n × n` array and `Det_n(A) ≠ 0` (the promise), with `x ∈ L` exactly when
`Det_n(A) > 0`. The resultant is taken from an arbitrary `ResultantSystem` `𝓡`. -/
theorem theorem_1_11 (𝓡 : ResultantSystem) :
    (∀ L ∈ ParityP, ManyOneReduction L (ResPos 𝓡)) ∧
    ∃ c : ℕ, ∀ L ∈ ParityP, ∃ u : Word → Word, FunctionInP u ∧ ∀ x : Word,
      ∃ A : SymTensor, 1 ≤ A.n ∧ A.nonzeroEntries ≤ c * A.n ∧ A.det 𝓡 ≠ 0 ∧
        u x = A.encode ∧ (x ∈ L ↔ 0 < A.det 𝓡) := by sorry

end Supplement

end ResultantVNP
