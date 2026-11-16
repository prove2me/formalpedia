-- Prove2me | Theorems.Thm_PCNonBool_Supplement_theorem_8_8
-- name    : PCNonBool.Supplement.theorem_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:31:22.224995+00:00
-- url     : https://prove2.me/theorems/e0e400b3-ef0b-46b3-aca4-b09ad9aec514
-- title:
--   Theorem 8.8 — PC over $\{1,c\}$ refutes inconsistent $\mathbb F_p$-linear systems in size $m(np)^{O(1)}$
-- statement:
--   **Theorem 8.8.** There is an absolute constant $C\in\mathbb N$ such that the following holds. Let $\mathbb F$ be a field of characteristic $0$, $c\in\mathbb F\setminus\{0\}$ an element that is not a root of unity, $p$ a prime, and $m,n\ge1$. Every inconsistent system of $m$ linear equations in $n$ variables over $\mathbb F_p$, encoded as in (127) by $P_{\|\ell\|,b}(m_\ell)$ for each equation $\ell=b$, has a polynomial calculus refutation over $\mathbb F$ of size at most
--   $$m\cdot(np)^{C},$$
--   using the range axioms $(y_i-1)(y_i-c)$, $i\in[n]$.
--
--   Polynomial calculus over non-roots of unity thus simulates Gaussian elimination over $\mathbb F_p$; for the $\bmod p$ Tseitin contradictions, which need exponential size in the Boolean encoding over fields of characteristic $\ne p$, this is an exponential separation.
--
--   **Formalization Note** The refutation is taken in the base mission's model with no reduction; converting to the standard model at most doubles the size, which $C$ absorbs since $np\ge2$.
--
--   Differences from the source:
--   - reading: size m(np)^{O(1)} → m·(np)^C with one absolute C ∈ ℕ chosen before the field, c, p, m, n and the system; reason: the constants of the simulation are absolute
--   - encoding: a system of m linear equations ℓ = b over F_p, elements represented by integers {0, …, p − 1}; inconsistent → a list sys of m equations LinEq p n (coefficients and right side in ZMod p, represented by ZMod.val); LinInconsistent sys: no x ∈ (ZMod p)^n satisfies every equation; reason: the same objects
--   - encoding: a polynomial calculus refutation (axiom lines are axioms, ends in 1), lines not reduced → PCNonBool.IsRefutation LinearMap.id: axiom lines may be scalar multiples of axioms, the refutation contains the line 1, no reduction; reason: p.11 prescribes no reduction for these upper bounds; a scaled axiom line c·a is simulated by a and c·a + 0·a, zero lines can be deleted, and the sequence can be cut after its first 1, so the two models differ in size by a factor at most 2, which the constant absorbs (see the item's Formalization Note)
--   - encoding: c ∈ F ∖ {0} is not a root of unity → c ≠ 0 and c^j ≠ 1 for every j ≥ 1; reason: the definition
--   - encoding: any field F → F : Type (universe 0); reason: Lean convention; the constant precedes the quantifier over fields, so they range over one universe; a refutation over F uses finitely many scalars, hence is a refutation of the same size over the countable subfield they generate, which is isomorphic to a field in Type
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 8.8, p.65 (PDF p.68); encoding (127), p.65 (PDF p.68)

import Mathlib
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_Supplement_LinEqEncoding

namespace PCNonBool.Supplement

/-- **Theorem 8.8** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.65 (PDF p.68)). Let `m, n ≥ 1`. Every inconsistent system of `m`
linear equations in `n` variables over `𝔽_p` encoded as in (127) has a polynomial calculus
refutation over `F` of size `m(np)^{O(1)}`, using the range axioms `(y_i - 1)(y_i - c)`.

Here (§8.2, p.65) `F` is a field of characteristic zero, `c ∈ F ∖ {0}` is not a root of unity and
`p` is a prime.

**Formalization Note** `m(np)^{O(1)}` is `m · (np)^C` with one absolute `C ∈ ℕ` chosen before the
field, `c`, `p`, `m`, `n` and the system. The refutation is in the base mission's model
(`PCNonBool.IsRefutation`) with no reduction modulo the range axioms (`red = id`). -/
theorem theorem_8_8 : ∃ C : ℕ,
    ∀ (F : Type) [Field F] [CharZero F] (c : F), c ≠ 0 → (∀ j : ℕ, 1 ≤ j → c ^ j ≠ 1) →
    ∀ (p : ℕ), p.Prime → ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
    ∀ sys : List (LinEq p n), sys.length = m → LinInconsistent sys →
      ∃ ρ : List (MvPolynomial (Fin n) F),
        PCNonBool.IsRefutation LinearMap.id (linAxioms c sys) ρ ∧
        PCNonBool.pcSize ρ ≤ m * (n * p) ^ C := by sorry

end PCNonBool.Supplement
