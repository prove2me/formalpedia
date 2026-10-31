-- Prove2me | Theorems.Thm_PeriodicEval_M_supermartingale
-- name    : PeriodicEval.M_supermartingale
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:39.410467+00:00
-- url     : https://prove2.me/theorems/d9d01efc-a1ec-4a82-b671-dc17053f631d
-- title:
--   Proof of Theorem 1, (26)–(27) — the conditional problem and the supermartingale $M_n$
-- statement:
--   Under the standing assumptions, let $x>0$, $X\in\mathcal A_0(x)$, $A^*$ the fixed point of $\Phi$, and
--
--   $$M_n:=\sum_{i=1}^ne^{-\beta T_i}U(X_{T_i}-\gamma X_{T_{i-1}})+A^*e^{-\beta T_n}X^\alpha_{T_n}.$$
--
--   For every $n$:
--
--   1. (26) $\sup_{Y\in L_{T_n,T_{n+1}}(1)}E[U(Y-\gamma)+A^*Y^\alpha\mid\mathcal F_{T_n}]=F(A^*)$: each such conditional expectation is at most $F(A^*)$ almost surely, and no constant smaller than $F(A^*)$ bounds them all;
--   2. (26) for the period return of $X$: $E[U(X_{T_{n+1}}-\gamma X_{T_n})+A^*X^\alpha_{T_{n+1}}\mid\mathcal F_{T_n}]\le F(A^*)X^\alpha_{T_n}$;
--   3. (27) $M$ is a supermartingale for $\mathcal G_n:=\mathcal F_{T_n}$: $M_n$ is $\mathcal G_n$-measurable and integrable and $E[M_{n+1}\mid\mathcal F_{T_n}]\le M_n$.
--
--   This is the verification step: it gives $V(x)\le A^*x^\alpha$.
--
--   **Formalization Note** $F$ is extended-real valued (finite at $A^*$) and conditional expectations are compared with it in the extended reals. Item 2 multiplies (26) through by $X^\alpha_{T_n}$ instead of dividing by $X_{T_n}$. A discrete-time supermartingale is stated through its one-step inequality.
--
--   Differences from the source:
--   - reading: sup_{Y ∈ L_{Tn,Tn+1}(1)} E[U(Y − γ) + A*Y^α | F_{Tn}] = F(A*) → every such conditional expectation is ≤ F(A*) a.s., and no constant c < F(A*) bounds them all a.s.; reason: the conditional supremum is an essential supremum; this states that it is the constant F(A*)
--   - encoding: (26) for Y = X_{T_{n+1}}/X_{T_n} → multiplied through by X^α_{T_n}; reason: avoids dividing by X_{T_n}; on {X_{T_n} > 0} it is (26) times a positive factor, and on {X_{T_n} = 0} both sides vanish
--   - encoding: M is a {G_n}-supermartingale → measurability, integrability and the one-step inequality E[M_{n+1} | F_{T_n}] ≤ M_n; reason: equivalent in discrete time by the tower property
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, eqs. (26)–(27), pp.42–43

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- (26)–(27), SSRN 3971852 (June 20, 2023), proof of Theorem 1, pp.42–43. For `x > 0`,
`X ∈ A_0(x)` and `A*` the fixed point of `Φ`, let
`M_n := ∑_{i=1}^n e^{−βT_i}U(X_{T_i} − γX_{T_{i−1}}) + A* e^{−βT_n} X^α_{T_n}`. Then, for every `n`,
1. (26), the conditional problem: `sup_{Y ∈ L_{T_n,T_{n+1}}(1)} E[U(Y − γ) + A*Y^α | ℱ_{T_n}] = F(A*)`,
   i.e. every such conditional expectation is at most `F(A*)` almost surely, and no constant
   smaller than `F(A*)` bounds them all;
2. (26), applied to `Y = X_{T_{n+1}}/X_{T_n}`:
   `E[U(X_{T_{n+1}} − γX_{T_n}) + A* X^α_{T_{n+1}} | ℱ_{T_n}] ≤ F(A*) X^α_{T_n}`;
3. (27): `M` is a `{𝒢_n}`-supermartingale, `𝒢_n := ℱ_{T_n}`: each `M_n` is `ℱ_{T_n}`-measurable and
   integrable, and `E[M_{n+1} | ℱ_{T_n}] ≤ M_n`.

**Formalization Note** The conditional supremum (an essential supremum) is rendered by its two
halves in item 1. Item 2 is (26) multiplied through by `X^α_{T_n}`: the paper divides by
`X_{T_n}`, which may vanish (on `{X_{T_n} = 0}` the supermartingale property of `ZX` forces
`X_{T_{n+1}} = 0`). `F` is `EReal`-valued (finite at `A*` by Proposition 4) and conditional
expectations are compared with it in `EReal`; conditioned variables are shown integrable so that
conditional expectations are genuine. The discrete-time supermartingale is stated through its
one-step inequality, equivalent by the tower property. -/
theorem M_supermartingale (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (X : ℝ≥0 → Ω → ℝ)
    (hX : X ∈ admissible p P ℱ B 0 x) (A : ℝ) (hA : Φ p P ℱ B A = (A : EReal)) :
    let M : ℕ → Ω → ℝ := fun n ω =>
      (∑ i ∈ Finset.range n, Real.exp (-(p.β * (p.T (i + 1) : ℝ))) *
          U p (X (p.T (i + 1)) ω - p.γ * X (p.T i) ω)) +
        A * Real.exp (-(p.β * (p.T n : ℝ))) * X (p.T n) ω ^ p.α
    (∀ n : ℕ, ∀ Y ∈ L p P ℱ B (p.T n) (p.T (n + 1)) 1,
      Integrable (fun ω => U p (Y ω - p.γ) + A * Y ω ^ p.α) P ∧
      ∀ᵐ ω ∂P, ((P[fun ω => U p (Y ω - p.γ) + A * Y ω ^ p.α | ℱ (p.T n)] ω : ℝ) : EReal) ≤
        F p P ℱ B A) ∧
    (∀ n : ℕ, ∀ c : ℝ, (c : EReal) < F p P ℱ B A →
      ∃ Y ∈ L p P ℱ B (p.T n) (p.T (n + 1)) 1,
        ¬ (∀ᵐ ω ∂P, P[fun ω => U p (Y ω - p.γ) + A * Y ω ^ p.α | ℱ (p.T n)] ω ≤ c)) ∧
    (∀ n : ℕ,
      Integrable (fun ω => U p (X (p.T (n + 1)) ω - p.γ * X (p.T n) ω) +
        A * X (p.T (n + 1)) ω ^ p.α) P ∧
      ∀ᵐ ω ∂P,
        ((P[fun ω => U p (X (p.T (n + 1)) ω - p.γ * X (p.T n) ω) + A * X (p.T (n + 1)) ω ^ p.α
            | ℱ (p.T n)] ω : ℝ) : EReal) ≤
          F p P ℱ B A * ((X (p.T n) ω ^ p.α : ℝ) : EReal)) ∧
    (∀ n : ℕ, StronglyMeasurable[ℱ (p.T n)] (M n)) ∧
    (∀ n : ℕ, Integrable (M n) P) ∧
    (∀ n : ℕ, P[M (n + 1) | ℱ (p.T n)] ≤ᵐ[P] M n) := by sorry

end PeriodicEval
