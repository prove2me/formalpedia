-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_logarithmic_design_code
-- name    : SubspaceEvasion312.Explicit.Supplement.logarithmic_design_code
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:08.418207+00:00
-- url     : https://prove2.me/theorems/c5028ee7-35b1-40f1-a933-b6596929f33b
-- title:
--   Corollary 22 — Guruswami–Kopparty design codes of rate 1/(3+3 log₂ ℓ)
-- statement:
--   There are absolute constants $K,h$ such that for every finite field $\mathbb F_q$ there is one encoder program $P$ with the following property. For all integers $r\ge1$, $\ell\ge1$ and $n$ with $n>4\ln\ell$ and $q>4nr$, there are an $\mathbb F_q$-additive code $C\subseteq(\mathbb F_q^{s})^n$ with $s=2r$, an encoder $\mathrm{Enc}$ of $C$ and a design function $\tau$ such that
--
--   $$\mathrm{rate}(C)\ge\frac1{3+3\log_2\ell},\qquad C\text{ is a }\tau\text{-subspace design},\qquad \tau(r)<\frac1{1+\log_2\ell},$$
--
--   $C$ is $(r,0,\ell,2\ell)$ subspace list-recoverable, and $P$, given $r,\ell,n$ and a message $x$, outputs $\mathrm{Enc}(x)$ within charged time and word bound $K\,n\,(r+\lfloor\log_2 q\rfloor+\lfloor\log_2\ell\rfloor+2)^h$.
--
--   This is the Case B code family of Theorem 25. The list-recovery clause is for the given $\ell$ only.
--
--   **Formalization Note** The hypothesis $n>4\log\ell$ has no stated base; the natural logarithm is used, which is the weaker hypothesis and so gives the stronger statement. Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - reading: r, ℓ ∈ N → 1 ≤ r and 1 ≤ ℓ; reason: log₂ 0 is undefined, and s = 2r = 0 leaves no code of positive rate
--   - reading: n > 4 log ℓ (base not stated) → 4 · Real.log ℓ < n (natural logarithm); reason: the weakest hypothesis among the readings, so the theorem implies the base-2 reading; true since an admissible rate exists once n ≥ 3(1+log₂ ℓ)/(r+3)
--   - reading: can be computed in time n · poly(r, log q, log ℓ) → one encoder program per field with inputs r, ℓ, n; charged time and word bound K·n·(r + ⌊log₂ q⌋ + ⌊log₂ ℓ⌋ + 2)^h with absolute K, h; reason: printed p. 7 encodability; a generator matrix is too large for this time
--   - encoding: explicit τ subspace-design additive code C ⊆ (F_q^s)^n, s = 2r → ∃ k, C : Code F (2r) n, E with IsEncoder C E, τ with SubspaceDesign C τ; reason: the mission's published definitions
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Corollary 22, printed p. 11 (PDF p. 12); from Theorem 20 ([GK16]) and Corollary 16

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit.Supplement
open scoped ENNReal
/-- Corollary 22, printed p.11 (PDF p.12). The hypothesis n > 4 log ell is read with
the natural logarithm (the weaker hypothesis); log2 in the conclusion is base two.
One encoder program per field takes r, ell and n; absolute K and h. -/
theorem logarithmic_design_code :
    ∃ K h : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F], ∃ enc : Program F,
    ∀ r ℓ n : ℕ, 1 ≤ r → 1 ≤ ℓ → 4 * Real.log (ℓ : ℝ) < (n : ℝ) →
      4 * n * r < Fintype.card F →
    ∃ (k : ℕ) (C : Code F (2 * r) n) (E : Vec F k →ₗ[F] Blocks F (2 * r) n)
      (τ : ℕ → ℝ),
      IsEncoder C E ∧ 1 / (3 + 3 * log₂ (ℓ : ℝ)) ≤ codeRate C ∧
      SubspaceDesign C τ ∧ τ r < 1 / (1 + log₂ (ℓ : ℝ)) ∧
      ListRecoverable C r 0 ℓ (2 * ℓ) ∧
      ∀ x : Vec F k, RunsWithin enc [r, ℓ, n] (vectorData x)
        (K * n * (r + Nat.log 2 (Fintype.card F) + Nat.log 2 ℓ + 2) ^ h)
        (K * n * (r + Nat.log 2 (Fintype.card F) + Nat.log 2 ℓ + 2) ^ h)
        (blockData (E x)) := by sorry
end SubspaceEvasion312.Explicit.Supplement
