-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_rate_preserving_lift
-- name    : QuantumGroupCodes836.Addressability.rate_preserving_lift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:12.769622+00:00
-- url     : https://prove2.me/theorems/8f6d84d9-5a8a-47fc-b5e2-0b26b6e09d62
-- title:
--   Theorem 4.1 — rate-preserving quasi-abelian lift
-- statement:
--   Fix a prime power $q>4$. There are positive constants $\alpha_q,\beta_q$, independent of the function field and code. Let $F/\mathbb F_q$ have genus $g>1$, full constants, and $N(F)>2g$. Let $P$ sum $n>2g$ rational places and let $D$ be effective, disjoint from $P$, with $2g-2<\deg D<n$. Assume the positive-degree multiplication divisor inequality with a differential having simple poles at every rational place of $F$. Then an actual quadratic-constant-field AG lift exists with
--
--   $$\alpha_q n\le\log|G|\le\beta_q n.$$
--
--   It preserves the code and dual rates and designed relative distances, is quasi-abelian, and the code and dual are free modules of ranks $k$ and $n-k$. The multiplication property is preserved. No starting family is assumed.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - reading: C̃ and C̃^⊥ have the same rate and designed relative distance as C and C^⊥ → ñ = n|G|, k̃ = k|G|, d(C̃) ≥ (n − deg D)|G|, k̃^⊥ = (n − k)|G|, d(C̃^⊥) ≥ (deg D − 2g + 2)|G|; reason: the designed distances n − deg D and deg D − 2g + 2 scaled by |G| over length n|G| give the same designed relative distances; realized distances are bounded, not equated
--   - generalization: an AG code C̃ = C_L(P̃,D̃) over F_{q²} which is quasi-G for G abelian → the full Corollary 4.5 data (conorm divisors, unramified separable Galois lift, coordinate action matching the place action); reason: Theorem 4.1 is proved from Corollary 4.5; the Lean conclusion implies the source one
--   - encoding: an integer m and a differential η with the stated simple poles → 0 < m and η ≠ 0 (inside AGAssumptions); reason: Definition 2.7 defines the m-multiplication property, which the theorem asserts, only for m ≥ 1; the zero differential has no divisor or poles
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 4.1, pp.14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem rate_preserving_lift (q : ℕ) (hq : 4 < q)
    (hPrimePower : ∃ p s : ℕ, p.Prime ∧ 0 < s ∧ q = p ^ s) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ (k : Type) [Field k] [Fintype k],
      Fintype.card k = q → ∀ (F : FunctionFieldData k) (P : EvaluationData F)
      (D : Divisors F) (m : ℕ) (η : KaehlerDifferential k F.carrier),
      1 < genus F → 2 * genus F < Nat.card {R : Places F // R.deg = 1} →
      2 * genus F < P.n → effective D → AGAssumptions P D m η →
      (∀ R : Places F, R.deg = 1 → R.ordDifferential η = -1) →
      ∃ L : LiftData F, LiftCodeProperties P D m L ∧
        α * P.n ≤ Real.log (Nat.card L.group) ∧ Real.log (Nat.card L.group) ≤ β * P.n := by sorry

end QuantumGroupCodes836.Addressability
