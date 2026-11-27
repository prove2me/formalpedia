-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_theorem_5
-- name    : RiskBalancingMNL.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:59:57.034597+00:00
-- url     : https://prove2.me/theorems/4b3ed07b-2e16-522d-9f99-4a87a87e268a
-- title:
--   Theorem 5 (corrected: (i) on $Q_0\ge1-\bar\lambda$, typo in (30)) — nested logit with common $b,\tau$: equal markup, Lambert W, the root of the first-order equation, zero past $\bar\lambda$
-- statement:
--   Consider the nested logit model with $K\ge1$ nonempty nests, and suppose every nest has the same price coefficient $b>0$ and the same dissimilarity index $\tau\in(0,1]$. Put $S=\sum_k(\sum_je^{a_{jk}-bc_{jk}})^\tau$, $\bar\lambda=S/(1+S)$ and $\hat m(Q_0)=\frac1{b\tau}[\log S+\log\frac{Q_0}{1-Q_0}]$.
--
--   1. **Equal markup and (30).** For every $\lambda\in[0,1)$ every optimal markup vector puts the same markup $t$ on all products of all nests, and $t>0$ when $\lambda<\bar\lambda$. An equal markup $t$ is feasible iff $t\ge0$; its no-purchase probability is $Q_0=1/(1+Se^{-b\tau t})$, and $\hat m(Q_0)=t$; and
--   $$
--   \pi=t(1-Q_0),\qquad g=t^2(1-Q_0),\qquad \tilde L(Q_0)=\pi^2-\lambda g=t^2(1-Q_0)(1-Q_0-\lambda). \tag{30}
--   $$
--   2. **(i) Unimodality.** For $\lambda\in[0,\bar\lambda)$ the first-order equation $\hat m(Q_0)-\frac1{b\tau Q_0}+\frac{\lambda\hat m(Q_0)}{2(1-Q_0-\lambda)}=0$ has exactly one root $x\in(0,1-\lambda)$, and $\tilde L$ is strictly increasing on $[1-\bar\lambda,x]$ and strictly decreasing on $[x,1-\lambda)$. For $\lambda\in[\bar\lambda,1)$, $\tilde L$ is strictly decreasing on $(0,1-\lambda)$.
--   3. **(ii) The optimal markup.** At $\lambda=0$ the markup
--   $$
--   m^*(0)=\frac1{b\tau}\Big[1+W\Big(e^{-1}\sum_k\Big(\sum_{j}e^{a_{jk}-bc_{jk}}\Big)^\tau\Big)\Big]
--   $$
--   ($W$ the Lambert W function) is optimal and maximizes the expected profit over all markup vectors. For $\lambda\in(0,\bar\lambda)$ the equation $\hat m(Q_0)-\frac1{b\tau Q_0}+\frac{\hat m(Q_0)}{2[(1-Q_0)/\lambda-1]}=0$ has exactly one root $Q_0^*(\lambda)\in(0,1-\lambda)$, its left side is strictly increasing on $(0,1-\lambda)$, and the markup
--   $$
--   m^*(\lambda)=\frac1{b\tau}\Big[\log\sum_k\Big(\sum_je^{a_{jk}-bc_{jk}}\Big)^\tau+\log\frac{Q_0^*(\lambda)}{1-Q_0^*(\lambda)}\Big] \tag{31}
--   $$
--   is optimal, with no-purchase probability $Q_0^*(\lambda)$. For $\lambda\in[\bar\lambda,1)$ the zero markup (selling at cost) is optimal. For every $\lambda\in[0,1)$ the optimal solution is unique.
--   4. **(iii) Monotonicity.** $Q_0^*(\lambda)$ and $m^*(\lambda)$ are nonincreasing in $\lambda$ on $[0,1)$ and strictly decreasing on $[0,\bar\lambda)$.
--
--   This is the nested logit counterpart of Lemmas 2–3, Theorem 1 and Corollary 1 for the MNL model: with common $b$ and $\tau$ the nested problem reduces to the symmetric MNL problem with $b$ replaced by $b\tau$ and $\sum_ie^{a_i-bc_i}$ by $S$.
--
--   **Formalization Note** Optimality is over all markup vectors with $\pi\ge0$. The printed (i) claims unimodality on $[0,1-\lambda)$, which fails below the feasible range $Q_0\ge1-\bar\lambda$; the printed middle expression of (30) has $\lambda m^2(1-Q_0)^2$ for $\lambda m^2(1-Q_0)$. Both are corrected.
--
--   Differences from the source:
--   - correction: (i) L̃(Q₀) is unimodal in Q₀ for all Q₀ ∈ [0, 1 − λ) → for λ ∈ [0, λ̄) with x the root of the first-order equation in (0, 1 − λ): L̃ strictly increasing on [1 − λ̄, x] and strictly decreasing on [x, 1 − λ); for λ ∈ [λ̄, 1), L̃ strictly decreasing on (0, 1 − λ) (the printed claim there, Q₀ = 0 excluded since m̂(0) is undefined); reason: for K = 1, M₁ = 1, τ = b = 1, a = c = 0, λ = 0: L̃(0.01) ≈ 20.69 > L̃(0.5) = 0 < L̃(0.8) ≈ 0.077, so L̃ is not unimodal on [0, 1); below 1 − λ̄ the markup m̂ is negative and infeasible; the same correction as the published RiskBalancingMNL.lemma_3
--   - correction: (30): π² − λg = m²(1 − Q₀)² − λm²(1 − Q₀)² = m²(1 − Q₀)(1 − Q₀ − λ) → π = t(1 − Q₀), g = t²(1 − Q₀) and L = t²(1 − Q₀)(1 − Q₀ − λ); the printed middle expression is not stated; reason: the middle expression is a typo for m²(1 − Q₀)² − λm²(1 − Q₀): at m = 1, Q₀ = λ = 1/2 it equals 1/8 while the last expression is 0
--   - reading: τ_k = τ with τ_k ∈ [0, 1] → 0 < τ (τ ≤ 1 from the model); reason: 1/(bτ) in (ii) and (31) is undefined at τ = 0
--   - reading: equal markup holds → for λ ∈ [0, 1) every optimal markup vector is constant over all products and nests, with a positive value for λ < λ̄; reason: the claim is about the optimal solution of problem (6), as Lemma 1 for the MNL model
--   - reading: the problem is equivalent to optimizing L̃(Q₀) → equal markup at the optimum, feasibility of an equal markup t iff t ≥ 0, Q₀(t) = 1/(1 + Se^{−bτt}), m̂(Q₀(t)) = t and (30); reason: these identities make the problem over equal markups the problem over Q₀
--   - reading: let Q₀*(λ) and m*(λ) be the optimal no-purchase probability and markup → the optimal solution is unique for every λ ∈ [0, 1); reason: as the published goal's reading of Theorem 1
--   - reading: unimodal → strictly increasing up to the root of the first-order equation and strictly decreasing after it; reason: the paper does not define the term; same reading as the published lemma_3
--   - reading: Q₀*(λ) solves the first-order equation, whose left side monotonically increases in Q₀ → for λ ∈ (0, λ̄): exactly one root in (0, 1 − λ), the left side strictly increasing on (0, 1 − λ), and every such root gives an optimal equal markup (31) with no-purchase probability equal to the root; reason: the equation is meaningful on (0, 1 − λ), the range given by (10)
--   - reading: (iii) both Q₀*(λ) and m*(λ) decrease in λ → weakly decreasing on [0, 1) and strictly decreasing on [0, λ̄); reason: on [λ̄, 1) both are constant (m* = 0)
--   - reading: the profit-maximizing markup m*(0) → m*(0) is optimal at λ = 0 and π(m') ≤ π(m*(0)) for every markup vector m'; reason: profit-maximizing means maximal expected profit, as in the published goal
--   - generalization: the root of the first-order equation for λ ∈ (0, λ̄) (ii) → a unique root of the λ = 0-safe first-order expression for every λ ∈ [0, λ̄), in clause (i); reason: at λ = 0 the root is the no-purchase probability of the Lambert W markup; for λ > 0 the two forms agree
--   - encoding: first-order expression with the last term m̂/(2[(1 − Q₀)/λ − 1]) → in (i): λm̂/(2(1 − Q₀ − λ)); in (ii) the printed form; reason: the forms agree for λ > 0; the first is defined at λ = 0
--   - encoding: K nests of M_k products; (Σ_j e^{a_jk − bc_jk})^τ; λ̄ with b_k and τ → products Σ k, Fin (M k), K ≥ 1, every nest nonempty; exp(τ_k log Σ_j e^{a_jk − b_k c_jk}) with b_k = b, τ_k = τ; reason: the same numbers for the instances of the paper
--   - encoding: problem (6) over share vectors q → IsOptimal over all markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between markups and shares (p.9), as in the published base mission
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §6, Theorem 5 with (30) and (31), p.24; the NL model, pp.22–23

import Mathlib
import Definitions.Def_RiskBalancingMNL_lambertW
import Definitions.Def_RiskBalancingMNL_Supplement_NLParams
import Definitions.Def_RiskBalancingMNL_Supplement_NLParams_mass

namespace RiskBalancingMNL.Supplement

open NLParams

/-- **Theorem 5 (nested logit with common `b` and `τ`)**, Li & Webster, *Optimizing Risk-balancing
Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), p.24. Suppose `bₖ = b` and
`τₖ = τ > 0` for every nest. Write `S = Σₖ (Σⱼ e^{aⱼₖ − bcⱼₖ})^τ`, `λ̄ = S/(1 + S)` and
`m̂(Q₀) = (1/(bτ))[log S + log(Q₀/(1 − Q₀))]`.
* (E) Equal markup holds: for `λ ∈ [0, 1)` every optimal markup vector is constant across all
  products and nests, with a positive value when `λ < λ̄`. The problem is equivalent to optimizing
  (30): an equal markup `t` is feasible iff `t ≥ 0`; `Q₀(t) = 1/(1 + Se^{−bτt})` and `m̂(Q₀(t)) = t`;
  `π = t(1 − Q₀)`, `g = t²(1 − Q₀)` and `L = t²(1 − Q₀)(1 − Q₀ − λ)`.
* (i) For `λ ∈ [0, λ̄)`, the first-order equation (left side `foc`) has exactly one root `x` in
  `(0, 1 − λ)`, and `L̃` is strictly increasing on `[1 − λ̄, x]` and strictly decreasing on
  `[x, 1 − λ)`. For `λ ∈ [λ̄, 1)`, `L̃` is strictly decreasing on `(0, 1 − λ)`.
* (ii) At `λ = 0` the markup `m*(0) = (1/(bτ))[1 + W(e^{−1}S)]` is optimal and maximizes the
  expected profit over all markup vectors. For `λ ∈ (0, λ̄)` the printed equation
  `m̂(Q₀) − 1/(bτQ₀) + m̂(Q₀)/(2[(1 − Q₀)/λ − 1]) = 0` has exactly one root `Q₀*(λ)` in
  `(0, 1 − λ)`, its left side is strictly increasing there, and the markup (31) `m̂(Q₀*(λ))` is
  optimal with no-purchase probability `Q₀*(λ)`. For `λ ∈ [λ̄, 1)`, `m = 0` is optimal.
  The optimal solution is unique for every `λ ∈ [0, 1)`.
* (iii) `Q₀*(λ)` and `m*(λ)` decrease in `λ` on `[0, 1)`, strictly on `[0, λ̄)`.

**Formalization Note** Products are `Σ k, Fin (M k)`, `K ≥ 1`, every nest nonempty. Optimality is
over all markup vectors under `π ≥ 0`. `lambertW` is the principal branch on `[0, ∞)`. The printed
middle expression of (30), `m²(1 − Q₀)² − λm²(1 − Q₀)²`, is a typo for `m²(1 − Q₀)² − λm²(1 − Q₀)`
and is not stated. For `λ < λ̄`, (i) is stated on the feasible range `Q₀ ≥ 1 − λ̄`, as the published
`RiskBalancingMNL.lemma_3`: on `[0, 1 − λ)` the printed claim is false there. For `λ ≥ λ̄` the
printed claim holds on `(0, 1 − λ)` (`L̃` is strictly decreasing, its peak at the left end) and is
stated there; `Q₀ = 0`, where `m̂` is undefined, is excluded. -/
theorem theorem_5 {K : ℕ} [NeZero K] {M : Fin K → ℕ} (P : NLParams K M) (b τ : ℝ)
    (hbk : ∀ k, P.b k = b) (hτk : ∀ k, P.τ k = τ) (hτ : 0 < τ) :
    -- (E) equal markup and the reduction (30)
    ((∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ m, P.IsOptimal lam m → ∃ t : ℝ, m = constM t) ∧
      (∀ lam : ℝ, 0 ≤ lam → lam < P.lamBar → ∀ m, P.IsOptimal lam m →
        ∃ t : ℝ, 0 < t ∧ m = constM t) ∧
      (∀ t : ℝ, P.Feasible (constM t) ↔ 0 ≤ t) ∧
      (∀ t : ℝ, P.noPurchase (constM t) = 1 / (1 + P.mass * Real.exp (-(b * τ * t)))) ∧
      (∀ t : ℝ, P.mHat b τ (P.noPurchase (constM t)) = t) ∧
      (∀ lam t : ℝ,
        P.profit (constM t) = t * (1 - P.noPurchase (constM t)) ∧
        P.spread (constM t) = t ^ 2 * (1 - P.noPurchase (constM t)) ∧
        P.objective lam (constM t) =
          t ^ 2 * (1 - P.noPurchase (constM t)) * (1 - P.noPurchase (constM t) - lam))) ∧
    -- (i) unimodality of L̃ (corrected range)
    (∀ lam : ℝ, 0 ≤ lam → lam < P.lamBar →
      (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧ P.foc b τ lam x = 0) ∧
      ∀ x ∈ Set.Ioo 0 (1 - lam), P.foc b τ lam x = 0 →
        StrictMonoOn (P.LTilde b τ lam) (Set.Icc (1 - P.lamBar) x) ∧
        StrictAntiOn (P.LTilde b τ lam) (Set.Ico x (1 - lam))) ∧
    -- (i) for λ ∈ [λ̄, 1): L̃ is strictly decreasing on (0, 1 − λ) (unimodal, peak at the left end)
    (∀ lam : ℝ, P.lamBar ≤ lam → lam < 1 →
      StrictAntiOn (P.LTilde b τ lam) (Set.Ioo 0 (1 - lam))) ∧
    -- (ii) λ = 0: the Lambert W markup
    (P.IsOptimal 0
        (constM ((1 + RiskBalancingMNL.lambertW (Real.exp (-1) * P.mass)) / (b * τ))) ∧
      ∀ m' : (Σ k, Fin (M k)) → ℝ, P.profit m' ≤
        P.profit (constM ((1 + RiskBalancingMNL.lambertW (Real.exp (-1) * P.mass)) / (b * τ)))) ∧
    -- (ii) λ ∈ (0, λ̄): the root of the printed equation and the markup (31)
    (∀ lam : ℝ, 0 < lam → lam < P.lamBar →
      (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧
        P.mHat b τ x - 1 / (b * τ * x) + P.mHat b τ x / (2 * ((1 - x) / lam - 1)) = 0) ∧
      StrictMonoOn (fun x => P.mHat b τ x - 1 / (b * τ * x) +
        P.mHat b τ x / (2 * ((1 - x) / lam - 1))) (Set.Ioo 0 (1 - lam)) ∧
      ∀ x ∈ Set.Ioo 0 (1 - lam),
        P.mHat b τ x - 1 / (b * τ * x) + P.mHat b τ x / (2 * ((1 - x) / lam - 1)) = 0 →
        P.IsOptimal lam (constM (P.mHat b τ x)) ∧ P.noPurchase (constM (P.mHat b τ x)) = x) ∧
    -- (ii) λ ∈ [λ̄, 1): sell at cost
    (∀ lam : ℝ, P.lamBar ≤ lam → lam < 1 → P.IsOptimal lam (constM 0)) ∧
    -- uniqueness of the optimal solution
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ m m' : (Σ k, Fin (M k)) → ℝ,
      P.IsOptimal lam m → P.IsOptimal lam m' → m = m') ∧
    -- (iii) Q₀*(λ) and m*(λ) decrease in λ, strictly below λ̄
    (∀ lam lam' t t' : ℝ, 0 ≤ lam → lam < lam' → lam' < 1 →
      P.IsOptimal lam (constM t) → P.IsOptimal lam' (constM t') →
      t' ≤ t ∧ P.noPurchase (constM t') ≤ P.noPurchase (constM t)) ∧
    (∀ lam lam' t t' : ℝ, 0 ≤ lam → lam < lam' → lam' < P.lamBar →
      P.IsOptimal lam (constM t) → P.IsOptimal lam' (constM t') →
      t' < t ∧ P.noPurchase (constM t') < P.noPurchase (constM t)) := by sorry

end RiskBalancingMNL.Supplement
