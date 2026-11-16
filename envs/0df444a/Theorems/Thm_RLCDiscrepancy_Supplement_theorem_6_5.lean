-- Prove2me | Theorems.Thm_RLCDiscrepancy_Supplement_theorem_6_5
-- name    : RLCDiscrepancy.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:54:10.033371+00:00
-- url     : https://prove2.me/theorems/9ab480c6-42b8-41fa-9718-6c3440d878d6
-- title:
--   Theorem 6.5 (corrected: Def. 6.2 linearity for (α, β) ≠ (0, 0)) — a linear locally leakage-resilient ramp scheme over $\mathbb F_q$ with thresholds $Rn\pm1.01n/\log q$
-- statement:
--   Fix a constant $R\in(0,1)$. There is $N$, depending only on $R$, such that for every $n\ge N$ and every prime $q$ with
--   $$
--   2^{800/R}\le q\le n^{0.19},
--   $$
--   there is a linear $(n,t_{\mathrm{rec}},t_{\mathrm{priv}},\varepsilon)$-locally leakage-resilient ramp secret sharing scheme over $\mathbb F_q$ (secrets and shares in $\mathbb F_q$) with
--   $$
--   Rn-\frac{1.01n}{\log q}\le t_{\mathrm{priv}}<t_{\mathrm{rec}}\le Rn+\frac{1.01n}{\log q}\qquad\text{and}\qquad \varepsilon\le4q^{-R^2n^{3/5}/3200}.
--   $$
--
--   This is the simplified form of Theorem 6.14: a gap of $O(n/\log q)$ between the thresholds with leakage error exponentially small in $n^{3/5}$.
--
--   **Formalization Note** The scheme is a secret sharing scheme in the sense of Definition 6.1 with a nonempty finite space of uniform coins, linear in the sense of Definition 6.2 with $m=1$ (§6 concerns linear ramp schemes, p.46); the thresholds are natural numbers.
--
--   Differences from the source:
--   - encoding: q prime, F_q → a finite field F with Fintype.card F prime; reason: every field of prime order q is F_q
--   - reading: unsubscripted log in §6 (log q, log(n(1−γ))) → Real.logb 2; reason: §6 never fixes the base; Lemma 6.13's bound h_q(ρ) ≤ ρ + 1/log q is the base-2 bound of [GRS25] and all §6 parameters are powers of 2; base 2 also gives the narrower threshold windows
--   - reading: an (n, t_rec, t_priv, ε)-locally leakage-resilient ramp secret sharing scheme over F_q → some RampScheme F n Ω (secrets and shares in F_q, nonempty finite uniform coins Ω) that is IsLinearScheme and IsLocallyLeakageResilient; reason: §6 is about linear ramp schemes (title; p.46 "We will be interested in linear ramp secret sharing schemes with m = 1, i.e., whose secrets and shares are elements of F_q"; p.47 the result addresses the open existence question for linear schemes), and the proof produces the Massey scheme; the linear reading is the stronger one
--   - correction: Definition 6.2's third clause for all α, β ∈ F_q → for (α, β) ≠ (0, 0); reason: at α = β = 0 it says the constant 0 has the law of Share(0), false for every scheme with non-constant shares (Massey scheme, Share(0) is uniform on C ≠ {0}), so as printed no such scheme is linear and Theorem 6.5 would be false
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 6.5, p.47

import Mathlib
import Definitions.Def_RLCDiscrepancy_Supplement_RampScheme
import Definitions.Def_RLCDiscrepancy_Supplement_IsLocallyLeakageResilient
import Definitions.Def_RLCDiscrepancy_Supplement_IsLinearScheme

universe u

namespace RLCDiscrepancy.Supplement

/-- **Theorem 6.5** (simplified version of Theorem 6.14). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 6.5, p.47: "Fix an arbitrary
constant R ∈ (0, 1). Given n ∈ N, let q be a prime satisfying 2^{800/R} ≤ q ≤ n^{0.19}. Then, for all
sufficiently large n (depending only on R) there is an (n, t_rec, t_priv, ε)-locally leakage-resilient
ramp secret sharing scheme over F_q with Rn − 1.01n/log q ≤ t_priv < t_rec ≤ Rn + 1.01n/log q and
ε ≤ 4q^{−R²n^{3/5}/3200}."

**Formalization Note.** Quantifiers: ∀ R ∈ (0, 1), ∃ N (depending on R only), ∀ n ≥ N, ∀ prime field
F_q in the range, ∃ scheme. F_q is a finite field `F` of prime cardinality q. A scheme "over F_q" has
secrets and shares in F_q and is linear (§6 is about linear ramp schemes; p.46: "We will be interested
in linear ramp secret sharing schemes with m = 1, i.e., whose secrets and shares are elements of F_q"):
a `RampScheme F n Ω` with a nonempty finite uniform coin space `Ω` (in the universe of `F`) satisfying
`IsLinearScheme` (Definition 6.2 with m = 1, its third clause required for (α, β) ≠ (0, 0), see that
definition) and Definitions 6.1, 6.4 with 1-bit local leakage. The thresholds are natural numbers. log is `Real.logb 2` (§6 convention: Lemma 6.13's bound
h_q(ρ) ≤ ρ + 1/log q, quoted from [GRS25], is the base-2 bound). Real powers are `Real.rpow`. -/
theorem theorem_6_5 :
    ∀ R : ℝ, 0 < R → R < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (F : Type u) [Field F] [Fintype F], (Fintype.card F).Prime →
      (2 : ℝ) ^ (800 / R) ≤ (Fintype.card F : ℝ) →
      (Fintype.card F : ℝ) ≤ (n : ℝ) ^ (0.19 : ℝ) →
      ∃ (Ω : Type u) (_ : Fintype Ω) (_ : Nonempty Ω) (P : RampScheme F n Ω)
        (tRec tPriv : ℕ) (ε : ℝ),
        R * n - 1.01 * n / Real.logb 2 (Fintype.card F) ≤ (tPriv : ℝ) ∧
        tPriv < tRec ∧
        (tRec : ℝ) ≤ R * n + 1.01 * n / Real.logb 2 (Fintype.card F) ∧
        ε ≤ 4 * (Fintype.card F : ℝ) ^ (-(R ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) / 3200)) ∧
        IsLinearScheme P ∧ IsLocallyLeakageResilient P tRec tPriv ε := by sorry

end RLCDiscrepancy.Supplement
