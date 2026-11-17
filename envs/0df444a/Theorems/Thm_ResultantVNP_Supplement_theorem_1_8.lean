-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_1_8
-- name    : ResultantVNP.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:58:23.534621+00:00
-- url     : https://prove2.me/theorems/809b4cd8-1d22-4c90-a915-ffc03e38d1ea
-- title:
--   Theorem 1.8 — $\mathrm{Res}^{(2)}_n \bmod 2^k$ and $\mathrm{Det}_n \bmod 2^k$ are $\#\mathsf P$-hard, and an addressed bit of a positive $\mathrm{Det}_n$ is $\mathsf{PP}$-hard
-- statement:
--   Let $k\ge1$ be given in unary and all integers in binary.
--
--   1. Given quadratic forms $f_1,\dots,f_n\in\mathbb Z[x]$, computing
--   $$\mathrm{Res}^{(2)}_n(f_1,\dots,f_n)\bmod 2^k$$
--   is $\#\mathsf P$-hard under polynomial-time counting many-one reductions: for every $\#\mathsf P$ function $f$ there are polynomial-time $u,v$ with $f(x)=v(x,\mathrm{ResMod}(u(x)))$.
--   2. The same holds for $\mathrm{Det}_n(A)\bmod 2^k$, with $A$ an integer symmetric tensor of order three.
--   3. Computing the addressed bit $\lfloor|\mathrm{Det}_n(A)|/2^j\rfloor\bmod 2$, with $j\ge0$ in unary, is $\mathsf{PP}$-hard under polynomial-time many-one reductions, even when $\mathrm{Det}_n(A)>0$: for every $\mathsf{PP}$ language $L$ a polynomial-time map sends each $x$ to an integer symmetric tensor $A$ of dimension $n\ge1$ with $\mathrm{Det}_n(A)>0$ and a unary $j$, such that $x\in L$ exactly when the addressed bit is $1$.
--
--   The resultant of integer quadratic forms can have exponentially many bits; the theorem shows that even its residue modulo a power of two, and a single bit of a positive tensor determinant, are hard to compute.
--
--   **Formalization Note** Instances and outputs are binary words, and $\#\mathsf P$ values are written in binary. Invalid words are mapped to the empty output. The resultant comes from an arbitrary resultant system.
--
--   Differences from the source:
--   - encoding: instances "with coefficients encoded in binary" → fixed injective codes (`QuadSystem.encode`, `SymTensor.encode`), with invalid words and $n=0$ mapped to the empty output; reason: a function problem needs a value on every word; valid inputs are unchanged.
--   - reading: "PP-hard … even when $\mathrm{Det}_n(A)>0$" → every PP language reduces through a map whose outputs are all codes of tensors with $\mathrm{Det}_n(A)>0$; reason: the standard meaning of hardness under a promise.
--   - encoding: "the resultant" → an arbitrary `ResultantSystem`; reason: all resultant systems agree with the unique resultant of Definition 2.1 for $n\ge1$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.8, p.7

import Mathlib
import Definitions.Def_ResultantVNP_Supplement_QuadSystem
import Definitions.Def_ResultantVNP_Supplement_SymTensor

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Theorem 1.8 (Hardness of modular evaluation).** Given quadratic forms `f₁, …, fₙ ∈ ℤ[x]` with
coefficients encoded in binary, and any integer `k ≥ 1` specified in unary, computing
`Res^{(2)}_n(f₁, …, fₙ) mod 2^k` is #P-hard under polynomial-time many-one (counting) reductions.
The modular hardness already holds for `Det_n(A)` with `A` an integer symmetric tensor of order
three. Computing an addressed bit `⌊|Det_n(A)|/2^j⌋ mod 2`, with `j ≥ 0` supplied in unary, is
PP-hard under polynomial-time many-one reductions, even when `Det_n(A) > 0`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.8, p.7 (proofs pp.20–21).

**Formalization Note** (1) and (2): every #P function `f` (its value written in binary,
`Nat.bits`) has a counting many-one reduction to `ResMod 𝓡`, resp. `DetMod 𝓡`. (3): for every PP
language `L` a polynomial-time `u` maps each word `x` to the code `⟨A, 1^j⟩` of a symmetric
integer tensor of dimension `≥ 1` with `Det_n(A) > 0` (the promise) whose addressed bit is `1`
exactly when `x ∈ L`. The resultant is taken from an arbitrary `ResultantSystem` `𝓡`. -/
theorem theorem_1_8 (𝓡 : ResultantSystem) :
    (∀ f ∈ SharpP, CountingReduction (fun x => (f x).bits) (ResMod 𝓡)) ∧
    (∀ f ∈ SharpP, CountingReduction (fun x => (f x).bits) (DetMod 𝓡)) ∧
    (∀ L ∈ PP, ∃ u : Word → Word, FunctionInP u ∧ ∀ x : Word,
      ∃ (A : SymTensor) (j : ℕ), 1 ≤ A.n ∧ 0 < A.det 𝓡 ∧
        u x = pairW A.encode (List.replicate j true) ∧
        (x ∈ L ↔ (A.det 𝓡).natAbs / 2 ^ j % 2 = 1)) := by sorry

end Supplement

end ResultantVNP
