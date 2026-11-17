-- Prove2me | Theorems.Thm_ProxGapTight_Supplement_theorem_4_1_concrete
-- name    : ProxGapTight.Supplement.theorem_4_1_concrete
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:08:30.250204+00:00
-- url     : https://prove2.me/theorems/5138e032-b553-4101-b343-a304e0d09b4b
-- title:
--   Theorem 4.1 — a concrete counterexample over $\mathbb F_{2^{128}}$ of length $2^{36}$ with more than $2^{54}$ exceptional coefficients
-- statement:
--   **Theorem 4.1 (a counterexample of concrete size).** Let $\mathbb F=\mathbb F_{2^{128}}$ be the field with $2^{128}$ elements and $N=2^{36}$. There are an $\mathbb F$-linear code $C\subseteq\mathbb F^{N}$ and vectors $f,g\in\mathbb F^{N}$ with the following properties.
--
--   1. **Code parameters.**
--   $$
--   0.4419<\delta(C)<0.4511,\qquad 0.5410875<R(C)<0.5502875.
--   $$
--   2. **Distance of the defining vectors.**
--   $$
--   \delta(f,C)>0.22945\quad\text{and}\quad\delta(g,C)>0.22945.
--   $$
--   3. **Exceptional coefficients.** At the radius $\rho:=0.1816$, which satisfies $\rho<\delta(C)/2$,
--   $$
--   |\mathcal Z_\rho(f,g;C)|>2^{54}.
--   $$
--
--   Here $\delta(C)=d(C)/N$ is the relative distance, $R(C)=\dim_{\mathbb F}C/N$ the rate, $\delta(x,C)$ the relative Hamming distance of $x$ to the nearest codeword, and $\mathcal Z_\rho(f,g;C)=\{z\in\mathbb F:\delta(f+zg,C)\le\rho\}$ the set of exceptional coefficients.
--
--   The theorem shows that the failure of proximity gaps for general linear codes, which Theorem 1.1 establishes asymptotically, already occurs at a field size, block length and rate used in practical SNARK constructions, and inside the unique-decoding radius: both $f$ and $g$ are far from $C$, yet more than $2^{54}$ of the $2^{128}$ combinations $f+zg$ are $0.1816$-close to it.
--
--   **Formalization Note** $\mathbb F_{2^{128}}$ is every field with $2^{128}$ elements; coordinates are indexed by $\mathrm{Fin}\,2^{36}$, and the code is an $\mathbb F$-submodule. The four quantities are the live mission's definitions; the decimals are exact real numbers and every inequality is strict, as printed.
--
--   Differences from the source:
--   - generalization: F_{2^128} → every field F with Fintype.card F = 2 ^ 128 (∀ F, ∃ C f g); reason: all fields of order 2^128 are isomorphic to F_{2^128}; the statement specializes to it
--   - encoding: coordinates [2^36]; δ(C), R(C), δ(x, C), 𝒵_ρ as in §2 → Fin (2 ^ 36); the base mission's relDist, rate (finrank over F), distToCode, exceptionalSet; reason: the same values
--   - encoding: δ(C) of the produced code presupposes C ≠ 0 → no separate C ≠ ⊥ conjunct; reason: 0.4419 < relDist C already excludes C = ⊥ (relDist ⊥ = 0)
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Theorem 4.1, p.15 (proof in Appendix A, pp.18–22)

import Mathlib
import Definitions.Def_ProxGapTight_relDist
import Definitions.Def_ProxGapTight_rate
import Definitions.Def_ProxGapTight_distToCode
import Definitions.Def_ProxGapTight_exceptionalSet

namespace ProxGapTight.Supplement

/-- **Theorem 4.1** (§4, a counterexample of concrete size; proof in Appendix A, pp.18–22),
Kominers, Thaler, Zheng, *The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General
Linear Codes*, manuscript (Sept. 2026), p.15.

"There are an F_{2^128}-linear code C ⊆ F_{2^128}^{2^36} and vectors f, g ∈ F_{2^128}^{2^36} with
the following properties.
• Code parameters. 0.4419 < δ(C) < 0.4511, 0.5410875 < R(C) < 0.5502875.
• Distance of the defining vectors. δ(f, C), δ(g, C) > 0.22945.
• Exceptional coefficients. At radius ρ := 0.1816 < δ(C)/2, we have |𝒵_ρ(f, g; C)| > 2^54"

**Formalization Note.**
* `F_{2^128}` is every field `F` with `Fintype.card F = 2 ^ 128` (all such fields are isomorphic
  to `F_{2^128}`; Mathlib's `GaloisField 2 128` carries no `Fintype` instance in this environment).
  The statement is `∀ F, ∃ C f g`.
* Coordinates are `Fin (2 ^ 36)`; "F_{2^128}-linear" is `C : Submodule F (Fin (2 ^ 36) → F)`, so
  the rate `R(C)` is `Module.finrank F C / 2^36` (dimension over `F_{2^128}`).
* `δ(C)`, `R(C)`, `δ(x, C)` and `𝒵_ρ(f, g; C) = {z : δ(f + z g, C) ≤ ρ}` are the base mission's
  `relDist`, `rate`, `distToCode`, `exceptionalSet`. The decimals are exact real literals; every
  inequality is strict, as printed. The clause `ρ := 0.1816 < δ(C)/2` is kept as a conjunct.
* `C ≠ ⊥` is not stated separately: `0.4419 < relDist C` already excludes it (`relDist ⊥ = 0`). -/
theorem theorem_4_1_concrete :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = 2 ^ 128 →
      ∃ C : Submodule F (Fin (2 ^ 36) → F), ∃ f g : Fin (2 ^ 36) → F,
        (0.4419 : ℝ) < relDist C ∧ relDist C < (0.4511 : ℝ) ∧
        (0.5410875 : ℝ) < rate C ∧ rate C < (0.5502875 : ℝ) ∧
        (0.22945 : ℝ) < distToCode f C ∧ (0.22945 : ℝ) < distToCode g C ∧
        (0.1816 : ℝ) < relDist C / 2 ∧
        (2 : ℝ) ^ 54 < ((exceptionalSet (0.1816 : ℝ) f g C).card : ℝ) := by sorry

end ProxGapTight.Supplement
