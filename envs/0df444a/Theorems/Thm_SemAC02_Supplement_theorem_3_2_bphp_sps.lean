-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_3_2_bphp_sps
-- name    : SemAC02.Supplement.theorem_3_2_bphp_sps
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:47:36.90408+00:00
-- url     : https://prove2.me/theorems/c1d2b1db-de0a-4afb-a655-047ce54c7c74
-- title:
--   Theorem 3.2 — semantic ΣΠΣ-PC refutations of BPHP^m_n need size 2^{Ω(n²/(mℓ²))}
-- statement:
--   Let $n=2^\ell$ for a sufficiently large integer $\ell$, and let $m>n$. Every arity-2 semantic ΣΠΣ-PC refutation $\pi$ of the bit pigeonhole principle $\mathrm{BPHP}^m_n$ over $\mathbb F_2$ has size
--
--   $$
--   2^{\Omega(n^2/(m\ell^2))}.
--   $$
--
--   The constant in $\Omega$ and the threshold for $\ell$ are absolute.
--
--   With the simulation of Theorem 2.3 this recovers exponential lower bounds for Res(⊕) refutations of $\mathrm{BPHP}^m_n$.
--
--   **Formalization Note** The size is measured by $S(\pi)$, the number of distinct non-zero product terms, which is at most the ΣΠΣ-size.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - generalization: size(π) ≥ 2^{Ω(n²/(mℓ²))} → S(π) = topS ≥ 2^{c n²/(mℓ²)}; reason: S(π) ≤ size(π) (p.16), so the bound on S(π) implies the bound on size; the proof bounds S(π)
--   - encoding: 2^{Ω(n²/(mℓ²))} for sufficiently large ℓ → ∃ c > 0, ∃ ℓ₀, ∀ ℓ ≥ ℓ₀, ∀ m > 2^ℓ; reason: asymptotic notation as explicit quantifiers, constants absolute
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 3.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_bphp

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 3.2** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong
Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 3.2, p.20): let `n = 2^ℓ` for a
sufficiently large integer `ℓ`, and let `m > n`. Any semantic ΣΠΣ-PC refutation of `BPHP^m_n`
over `𝔽₂` requires size `2^{Ω(n²/(mℓ²))}`.

**Formalization Note** `Ω` is an absolute constant `c > 0` and "sufficiently large" an absolute
threshold `ℓ₀`, both chosen before `ℓ` and `m`. The size is measured by `S(π)` (`topS`), which is
at most the `C`-size, so this is the stronger form. -/
theorem theorem_3_2_bphp_sps :
    ∃ c : ℝ, 0 < c ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef IsSPS Set.univ (polyAx (bphp m ℓ)) π →
        (2 : ℝ) ^ (c * ((2 : ℝ) ^ ℓ) ^ 2 / ((m : ℝ) * (ℓ : ℝ) ^ 2)) ≤ topS Set.univ π := by sorry

end SemAC02.Supplement
