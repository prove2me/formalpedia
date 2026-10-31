-- Prove2me | Theorems.Thm_PeriodicEval_theorem_1
-- name    : PeriodicEval.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:10:09.585359+00:00
-- url     : https://prove2.me/theorems/513291c0-0b85-4581-b50d-0f6192ea952f
-- title:
--   Theorem 1 — $V(x)=A^*x^\alpha$, $A^*$ the unique fixed point of $a\mapsto e^{-\beta\tau}F(a)$, and the optimal portfolio in four regimes
-- statement:
--   Assume the standing assumptions ($\sigma>0$, $\theta\ne0$, $\tau>0$, $\gamma\ge0$, $\alpha\in(0,1)$, $k\ge0$, $\beta>0$, $\beta>h$), and let $\mathcal F$ be the augmented natural filtration of the Brownian motion $B$. Let $F$ be the value (14) of the auxiliary problem and $\kappa=(k^{1/(1-\alpha)}+1)^{1-\alpha}$. Then:
--
--   1. the map $a\mapsto e^{-\beta\tau}F(a)$ has a unique fixed point $A^*$;
--   2. the value function of problem (4) is $V(x)=A^*x^\alpha$ for every $x>0$;
--   3. there are constants $0<c_1<1<c_2$ and $c_3>1$, depending on $A^*$, such that for every maximizer selection $y^*_{A^*}$ of $q\mapsto\arg\max_{y\ge0}(\bar G_{A^*}(y)-qy)$ there is $\lambda^*>0$ with:
--      (a) in Cases 1, 2a and 2b ($A^*>-\kappa$), $\lambda^*$ is the unique solution of $E[Z_\tau y^*_{A^*}(\lambda^*Z_\tau)]=1$;
--      (b) for every $x>0$ there is an optimal portfolio $X^*\in\mathcal A_0(x)$, with objective $A^*x^\alpha=V(x)$, $X^*_{T_0}=x$ and
--      $$X^*_{T_i}=X^*_{T_{i-1}}\,y^*_{A^*}\Big(\lambda^*\frac{Z_{T_i}}{Z_{T_{i-1}}}\Big),\qquad i=1,2,\dots\qquad(16)$$
--      (c) for every $i\ge1$ the support of $y^*_{A^*}(\lambda^*Z_{T_i}/Z_{T_{i-1}})$ is
--      $$\begin{cases}(0,c_1\gamma)\cup(c_2\gamma,\infty),&A^*>0\ \text{(Case 1)},\\\{0\}\cup(c_3\gamma,\infty),&-1\le A^*\le0\ \text{(Case 2a)},\\\{0\}\cup\big(c_3\gamma,\frac{\gamma}{1-|A^*|^{-1/(1-\alpha)}}\big),&-\kappa<A^*<-1\ \text{(Case 2b)},\\\{0\},&A^*\le-\kappa\ \text{(Case 3)}.\end{cases}$$
--
--   The theorem solves the infinite-horizon portfolio problem with periodic evaluation completely: the value is a power of wealth, its constant solves a one-dimensional fixed-point equation, and the optimal gross return in each period is an i.i.d. function of the pricing-kernel increment whose support shows whether the portfolio stays solvent, risks ruin, or is liquidated at once.
--
--   **Formalization Note** "Support" is read as: the variable lies in the set almost surely and every point of the set is charged. Every $\gamma\ge0$ and $k\ge0$ is covered; at $\gamma=0$ the fixed point is positive and the support is $(0,\infty)$.
--
--   Differences from the source:
--   - reading: 'the support of y*_{A*}(λ*Z_{T_i}/Z_{T_{i−1}}) is S' → SuppEq: the variable lies in S a.s. and every point of S is charged; reason: the topological support is closed while the printed sets are not (in Case 1 it contains 0); the paper uses the table for a.s. solvency and atoms at 0 (pp.19–20)
--   - reading: 'the optimal portfolio value process X* … is given by (16)' → there is an optimal X* ∈ A_0(x) (objective A*x^α = V(x)) satisfying (16); reason: the proof shows existence (p.43, 'it is sufficient to demonstrate the existence of some admissible process'); uniqueness fails at A* = −κ, where G_{A*} has two global maxima
--   - reading: 'standard filtered probability space supporting a Brownian motion', complete market → F is the augmented natural filtration of B; reason: market completeness (replication in the proof, p.44) needs a Brownian filtration
--   - generalization: the function y*_{A*} 'defined in Proposition 3' → every maximizer selection of q ↦ arg max_{y≥0}(Ḡ_{A*}(y) − qy); reason: the paper defines y*_a as this argmax (p.38) and its explicit choice is one selection; this also defines y* at γ = 0, where Proposition 3's constants are undefined
--   - encoding: S_t solving dS/S = μdt + σdB → closed form S₀exp((μ − σ²/2)t + σB_t) with S₀ > 0; reason: the unique solution; S₀ is unnamed in the paper and cancels
--   - encoding: V(x), F(a) as suprema → sSup in EReal; reason: no junk value for unbounded sets; finite values are the paper's
--   - encoding: E[Z_τ Y] ≤ 1 and E[Z_τ y*(λZ_τ)] = 1 → lower Lebesgue integrals of nonnegative variables; reason: the expectation of a nonnegative variable, without the Bochner convention for non-integrable functions
--   - encoding: admissible strategies with a.s. finite ∫(φ^(S)S)² du → pathwise integrability on every path (EthierKurtz.HasBrownianItoIntegral); reason: under the augmented filtration a strategy can be set to zero on the null set where it fails, keeping the same value processes a.s.
--   - encoding: time t ≥ 0 and the sum over i = 1, 2, … → time in ℝ≥0, T_i = (iτ).toNNReal, sum over i + 1 with i ∈ ℕ; reason: same dates and same series
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Theorem 1, pp.13–14 (eqs. (14), (16)); F defined in (14), y*_{A*} in Proposition 3, p.37 and its proof, p.38

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary
import Definitions.Def_PeriodicEval_Concavify
import Definitions.Def_PeriodicEval_SuppEq

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Theorem 1, SSRN 3971852 (June 20, 2023), pp.13–14. The value function of problem (4) is
`V(x) = A*x^α`, where `A*` is the unique fixed point of `a ↦ e^{−βτ}F(a)`. The optimal
portfolio value process satisfies `X*_{T_i} = X*_{T_{i−1}} y*_{A*}(λ*Z_{T_i}/Z_{T_{i−1}})`,
`i = 1, 2, …` (16), with `X*_{T_0} = x`. The support of `y*_{A*}(λ*Z_{T_i}/Z_{T_{i−1}})` is
`(0, c₁γ) ∪ (c₂γ, ∞)` if `A* > 0` (Case 1), `{0} ∪ (c₃γ, ∞)` if `−1 ≤ A* ≤ 0` (Case 2a),
`{0} ∪ (c₃γ, γ/(1 − |A*|^{−1/(1−α)}))` if `−κ < A* < −1` (Case 2b), and `{0}` if `A* ≤ −κ`
(Case 3), `κ = (k^{1/(1−α)} + 1)^{1−α}`, for some constants `0 < c₁ < 1 < c₂` and `c₃ > 1`
depending on `A*`. In Cases 1, 2a and 2b, `λ* > 0` is the unique solution of
`E[Z_τ y*_{A*}(λ*Z_τ)] = 1`.

**Formalization Note** Readings: "the optimal portfolio value process is given by (16)" is
the existence of an optimizer `X* ∈ A_0(x)` (objective `= A*x^α = V(x)`) of that form, which is
what the proof shows (p.43); "support" is `SuppEq` (almost surely in the set, every point of
the set charged); `y*_{A*}` is any maximizer selection of `q ↦ arg max_{y≥0}(Ḡ_{A*}(y) − qy)`
(p.38), of which Proposition 3's explicit function is one; `ℱ` is the augmented natural
filtration of `B`. Every `γ ≥ 0` and `k ≥ 0` is covered. -/
theorem theorem_1 (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) :
    (∃! A : ℝ, Φ p P ℱ B A = (A : EReal)) ∧
    ∀ A : ℝ, Φ p P ℱ B A = (A : EReal) →
      (∀ x : ℝ, 0 < x → V p P ℱ B x = ((A * x ^ p.α : ℝ) : EReal)) ∧
      ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ c₁ < 1 ∧ 1 < c₂ ∧ 1 < c₃ ∧
        ∀ y : ℝ → ℝ, IsArgmaxSelection (concaveMajorant (G p A)) y →
          ∃ lam : ℝ, 0 < lam ∧
            (-p.κ < A → ∀ l : ℝ, 0 < l →
              (∫⁻ ω, ENNReal.ofReal (Z p B p.τ.toNNReal ω * y (l * Z p B p.τ.toNNReal ω)) ∂P = 1
                ↔ l = lam)) ∧
            (∀ x : ℝ, 0 < x → ∃ X ∈ admissible p P ℱ B 0 x,
              objective p P X = A * x ^ p.α ∧ (∀ ω, X 0 ω = x) ∧
              ∀ i : ℕ, X (p.T (i + 1)) =ᵐ[P] fun ω =>
                X (p.T i) ω * y (lam * (Z p B (p.T (i + 1)) ω / Z p B (p.T i) ω))) ∧
            ∀ i : ℕ,
              let Yi : Ω → ℝ := fun ω => y (lam * (Z p B (p.T (i + 1)) ω / Z p B (p.T i) ω))
              (0 < A → SuppEq P Yi (Ioo 0 (c₁ * p.γ) ∪ Ioi (c₂ * p.γ))) ∧
              (-1 ≤ A ∧ A ≤ 0 → SuppEq P Yi ({0} ∪ Ioi (c₃ * p.γ))) ∧
              (-p.κ < A ∧ A < -1 → SuppEq P Yi ({0} ∪ Ioo (c₃ * p.γ) (p.ymax A))) ∧
              (A ≤ -p.κ → SuppEq P Yi {0}) := by sorry

end PeriodicEval
