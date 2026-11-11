-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_theorem_1_1
-- name    : RSBeyondJohnson.FirstOrder.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:04.674204+00:00
-- url     : https://prove2.me/theorems/566b020c-d033-41c5-a0fc-d101b9b2fa36
-- title:
--   Theorem 1.1 — first-order list decoding and MCA beyond Johnson
-- statement:
--   Fix $0<\rho<1$ and $a=a_1(\rho)+\eta_1<1$ with $\eta_1>0$. Let $n\ge2$, $2\le k\le\rho n$ and $an\le A\le n$ be integers, where $A$ is the required number of agreements. The explicit nonnegative integer $B_\partial=\lfloor\lambda_\partial m\rfloor$ of (28) satisfies $B_\partial=O_\rho((\eta_1+1/n)^{-1})$, and the following holds. Over every field $F$ of characteristic zero or $p>\max\{k-1,B_\partial\}$, and every set of $n$ distinct evaluation points $\alpha_1,\dots,\alpha_n$:
--
--   * every received word $y\in F^n$ has a finite agreement list $\mathcal L(y,A)$ (polynomials of degree $<k$ with at least $A$ agreements), of size $O_\rho(n/\eta_1^2)$;
--   * $\mathrm{RS}_\alpha[n,k]$ has line MCA with full agreement sets (Definition 3.2) at threshold $A$, with exceptional count $O_\rho(n^2/\eta_1^4)$: every received line $f+zg$ has one finite set $\mathcal E\subseteq F$ of that size outside which every degree-$<k$ $P$ with $|S_z(P)|\ge A$ is $F_0+zG_0$ with degree-$<k$ witnesses and $S_z(P)=S(F_0,G_0)$.
--
--   Precisely: for every $\rho\in(0,1)$ there is one constant $C_\rho>0$ such that for all such $\eta_1,n,k,A$,
--   $$B_\partial\le\frac{C_\rho}{\eta_1+1/n},\qquad|\mathcal L(y,A)|\le C_\rho\frac n{\eta_1^2},\qquad|\mathcal E|\le C_\rho\frac{n^2}{\eta_1^4}$$
--   for every field, evaluation set, word and line as above. The curve $a_1(\rho)$ lies strictly below the Johnson threshold $\sqrt\rho$, so this goes beyond Johnson at every rate.
--
--   Differences from the source:
--   - encoding: O_ρ(·) in B∂ = O_ρ((η₁ + 1/n)⁻¹), O_ρ(n/η₁²), O_ρ(n²/η₁⁴) → ∀ ρ ∈ (0,1), ∃ C > 0 (chosen before every other variable), ∀ …: … ≤ C · (rate of the O); reason: the paper's convention (p. 5): the subscript lists the only parameters the hidden constant may depend on
--   - reading: there is an explicit nonnegative integer B∂ = O_ρ((η₁ + 1/n)⁻¹) such that … → B∂ is the explicit integer bDel ρ a n = ⌊λ∂ m⌋ of (28), with B∂ ≤ C/(η₁ + 1/n); reason: the paper's explicit B∂ is that of (28) (Theorems 5.1, 5.2 and §5.4); naming the witness implies the existential
--   - encoding: field of characteristic zero or p > max{k − 1, B∂} → ringChar F = 0 ∨ max (k − 1) B∂ < ringChar F; reason: ringChar is the characteristic; same fields
--   - encoding: |L(y, A)| ≤ bound → (listDecodingSet k α y A).Finite ∧ ncard ≤ bound (reused RSListDecodingCapacity_AllRates_Decoding; zero polynomial included); reason: Set.ncard of an infinite set is 0; finiteness keeps the bound meaningful
--   - encoding: full agreement-set line MCA has exceptional count O_ρ(n²/η₁⁴) → HasLineMCA k α A (C n²/η₁⁴) (Definition 3.2: one Finset per line, chosen before z and P); reason: Definition 3.2 is exactly this property
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: every field F → every F : Type u (one universe, quantified inside the statement); reason: Lean universes; every field is isomorphic to one in the universe of its elements
--   - reading: Over F_q, divide the (exceptional) count by q for the soundness error → not a separate clause; reason: it interprets the count: |E|/q is the probability that a uniform challenge in F_q lies in E, immediate from the count bound
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 6, Theorem 1.1 (proved as Theorems 5.1–5.2, pp. 30–31, §5.4)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Theorem 1.1 (First-order list decoding and MCA)**, p. 6. For every rate bound
`0 < ρ < 1` there is a constant `C_ρ > 0` (depending on `ρ` only) such that for every `η₁ > 0`
with `a := a₁(ρ) + η₁ < 1` and all integers `n ≥ 2`, `2 ≤ k ≤ ρn`, `an ≤ A ≤ n`, the explicit
nonnegative integer `B∂ = ⌊λ∂ m⌋` of (28) satisfies `B∂ ≤ C_ρ/(η₁ + 1/n)`, and over every field
`F` of characteristic zero or `p > max{k − 1, B∂}` and every injective `α : Fin n → F`:
(i) every received word has a finite agreement list `L(y, A)` of size at most `C_ρ n/η₁²`;
(ii) `RS_α[n, k]` has line MCA with full agreement sets at threshold `A` with exceptional bound
`C_ρ n²/η₁⁴`. -/
theorem theorem_1_1.{u} :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ η₁ : ℝ, 0 < η₁ → a1 ρ + η₁ < 1 →
        ∀ n k A : ℕ, 2 ≤ n → 2 ≤ k → (k : ℝ) ≤ ρ * n → (a1 ρ + η₁) * n ≤ (A : ℝ) → A ≤ n →
          (bDel ρ (a1 ρ + η₁) n : ℝ) ≤ C / (η₁ + 1 / (n : ℝ)) ∧
          ∀ (F : Type u) [Field F],
            (ringChar F = 0 ∨ max (k - 1) (bDel ρ (a1 ρ + η₁) n) < ringChar F) →
            ∀ α : Fin n → F, Function.Injective α →
              (∀ y : Fin n → F,
                (RSListDecodingCapacity.AllRates.listDecodingSet k α y (A : ℝ)).Finite ∧
                ((RSListDecodingCapacity.AllRates.listDecodingSet k α y (A : ℝ)).ncard : ℝ) ≤
                  C * n / η₁ ^ 2) ∧
              HasLineMCA k α A (C * (n : ℝ) ^ 2 / η₁ ^ 4) := by sorry

end RSBeyondJohnson.FirstOrder
