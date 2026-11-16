-- Prove2me | Theorems.Thm_PCNonBool_Supplement_theorem_8_1
-- name    : PCNonBool.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:30:46.6703+00:00
-- url     : https://prove2.me/theorems/e55109ea-d8ed-437a-8187-e3ed8e260f55
-- title:
--   Theorem 8.1 — PC over $\{1,c\}$ simulates bounded-coefficient cutting planes in size $s\,t^{O(1)}$
-- statement:
--   **Theorem 8.1.** There is an absolute constant $C\in\mathbb N$ such that the following holds. Let $\mathbb F$ be a field of characteristic $0$ and $c\in\mathbb F\setminus\{0\}$ an element that is not a root of unity. If cutting planes refutes a set $\mathcal L=\{L_1,\dots,L_m\}$ of linear inequalities over $n$ Boolean variables in length $s$ and coefficient size $t$, then polynomial calculus over $\mathbb F$ with $\{1,c\}$-valued variables refutes the range-polynomial encoding
--   $$P_{c,\mathcal L}=\{p_{L_1},\dots,p_{L_m}\}\cup\{(y_i-1)(y_i-c): i\in[n]\}$$
--   in size at most $s\cdot t^{C}$.
--
--   Since cutting planes refutes the pigeonhole principle with small coefficients, this gives an exponential separation between polynomial calculus over non-roots of unity and over $\{\pm1\}$ or $\{0,1\}$ (Theorem 5.1).
--
--   **Formalization Note** The polynomial calculus refutation is taken in the base mission's model with no reduction modulo the range axioms, as p.11 prescribes for this simulation. That model allows scaled axiom lines and only asks that the line $1$ occurs; converting to the standard model at most doubles the size, which $C$ absorbs when $t\ge2$, and when $t=1$ the line $0\ge1$ is an initial inequality and $1$ is an axiom.
--
--   Differences from the source:
--   - reading: size s·t^{O(1)} → s·t^C with one absolute C ∈ ℕ chosen before the field, c, n, the inequalities and the cutting planes refutation; reason: the constants of the simulation are absolute
--   - encoding: cutting planes (4a)–(4e) on integer linear inequalities over {0,1}-variables → cutting planes over literals x_i, x̄_i with natural coefficients (Ineq n), literal axioms x_i ≥ 0 and x̄_i ≥ 0, addition followed by normalization (x_i + x̄_i ↦ 1), multiplication by c ∈ ℕ, division by c ≥ 1 dividing every coefficient with right side ⌈b/c⌉; length = number of lines; reason: the paper's own convention for this simulation (p.12: dual variables, nonnegative coefficients, normalized addition); an integer inequality is the same as a literal inequality after moving negative terms, which changes the coefficient size by a factor at most 2, absorbed by C
--   - reading: coefficient size: the sum of all coefficient magnitudes in the refutation → cpCoeffSize: ∑ over lines of (∑ a_i + ∑ ā_i + |b|), right-hand sides included; reason: with right-hand sides excluded the refutation [0 ≥ 1] of {0 ≥ 1} has t = 0, and the bound s·0^C = 0 is false for C ≥ 1 since every refutation has size ≥ 1; the reading including b is the only one under which the printed statement holds
--   - encoding: a cutting planes refutation: a derivation of 0 ≥ 1 → IsCPRefutation: a derivation that contains the line 0 ≥ 1; reason: cut the sequence after its first 0 ≥ 1; length and coefficient size do not grow
--   - generalization: P_L = {p_{L_1}, …, p_{L_m}} with p_L = ∏_{a ∈ Sat(L)} (m_ℓ − c^a) (98), for linear forms with natural coefficients → initial inequalities may contain negative literals x̄_i; each is encoded by Remark 8.5's dual-free p′_L = ∏_{a ∈ Sat(L)} (c^{d₂} m₁ − c^a m̄₂) (rangePoly), together with the range axioms (y_i − 1)(y_i − c); reason: when no initial inequality has a negative literal (ā = 0), p′_L is exactly (98)'s p_L, so the statement specializes to the paper's; Remark 8.5 extends the proof to dual literals
--   - reading: Sat(L) = [b, ‖ℓ‖], "the set of values in the (a priori) range of ℓ that can satisfy L" (97) → Ineq.sat: the natural numbers a with b ≤ a ≤ ‖ℓ‖ (empty when b > ‖ℓ‖, all of [0, ‖ℓ‖] when b ≤ 0); reason: the a priori range of ℓ is [0, ‖ℓ‖], as (97)'s own gloss says; the interval notation for b < 0 would add factors m_ℓ − c^a with a < 0, which the paper's description excludes
--   - encoding: a polynomial calculus refutation (axiom lines are axioms, ends in 1), lines not reduced → PCNonBool.IsRefutation LinearMap.id: axiom lines may be scalar multiples of axioms, the refutation contains the line 1, no reduction; reason: p.11 prescribes no reduction for these upper bounds; a scaled axiom line c·a is simulated by a and c·a + 0·a, zero lines can be deleted, and the sequence can be cut after its first 1, so the two models differ in size by a factor at most 2, which the constant absorbs (see the item's Formalization Note)
--   - encoding: c ∈ F ∖ {0} is not a root of unity → c ≠ 0 and c^j ≠ 1 for every j ≥ 1; reason: the definition
--   - encoding: any field F → F : Type (universe 0); reason: Lean convention; the constant precedes the quantifier over fields, so they range over one universe; a refutation over F uses finitely many scalars, hence is a refutation of the same size over the countable subfield they generate, which is isomorphic to a field in Type
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 8.1, p.58 (PDF p.61); Remark 8.5, p.62 (PDF p.65)

import Mathlib
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_Supplement_CuttingPlanes
import Definitions.Def_PCNonBool_Supplement_RangeEncoding

namespace PCNonBool.Supplement

/-- **Theorem 8.1** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.58 (PDF p.61)). If cutting planes can refute a set of linear
inequalities `{L₁, …, L_m}` in length `s` and coefficient size `t`, then polynomial calculus over a
field `F` of characteristic 0 with `{1, c}`-valued variables can refute `P_L = {p_{L₁}, …, p_{L_m}}`
in size `s t^{O(1)}`.

Here `c ∈ F ∖ {0}` is not a root of unity (§8.1, p.58), and `P_L = P_{c,L}` contains the range
axioms `(y_i - 1)(y_i - c)`.

**Formalization Note** `s t^{O(1)}` is `s · t^C` with one absolute `C ∈ ℕ` chosen before the field,
`c`, `n`, the inequalities and the cutting planes refutation. Cutting planes works over literals
with dual variables in normalized form (p.12); inequalities with negative literals are encoded by
Remark 8.5's dual-free `p'_L` (`rangePoly`). The polynomial calculus refutation is in the base
mission's model (`PCNonBool.IsRefutation`) with no reduction modulo the range axioms
(`red = id`, as p.11 prescribes for this simulation). -/
theorem theorem_8_1 : ∃ C : ℕ,
    ∀ (F : Type) [Field F] [CharZero F] (c : F), c ≠ 0 → (∀ j : ℕ, 1 ≤ j → c ^ j ≠ 1) →
    ∀ (n : ℕ) (Ls π : List (Ineq n)), IsCPRefutation Ls π →
      ∃ ρ : List (MvPolynomial (Fin n) F),
        PCNonBool.IsRefutation LinearMap.id (rangeAxioms c Ls) ρ ∧
        PCNonBool.pcSize ρ ≤ π.length * cpCoeffSize π ^ C := by sorry

end PCNonBool.Supplement
