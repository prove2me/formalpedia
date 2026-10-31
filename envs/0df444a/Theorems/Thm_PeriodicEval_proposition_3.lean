-- Prove2me | Theorems.Thm_PeriodicEval_proposition_3
-- name    : PeriodicEval.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:07.905352+00:00
-- url     : https://prove2.me/theorems/b12ff8ed-b219-4bc6-ad9b-67bf8e0a609f
-- title:
--   Proposition 3 — the optimizer $y^*_a(\lambda^*Z_\tau)$ of the auxiliary problem (corrected: $\gamma>0$ in Cases 1–2; Case 2 excludes $a=-1$, $k=0$)
-- statement:
--   Assume the standing assumptions (and $\gamma>0$ in Cases 1 and 2), and let $c_1,c_2,c_3,m_1,m_2$ be the constants of Lemma 2. The optimizer of problem (14) is $Y^*=y^*_a(\lambda^*Z_\tau)$, where:
--
--   1. if $a>0$: $y^*_a(q)=I_2(q)$ for $0<q\le m_1$ and $y^*_a(q)=I_1(q)$ for $q>m_1$, where $I_1(q)\in(0,c_1\gamma)$ is the solution of $\alpha[k(\gamma-y)^{\alpha-1}+ay^{\alpha-1}]=q$ on $(0,c_1\gamma)$ and $I_2(q)\in[c_2\gamma,\infty)$ the solution of $\alpha[(y-\gamma)^{\alpha-1}+ay^{\alpha-1}]=q$ on $[c_2\gamma,\infty)$;
--   2. if $-1\le a\le0$ with $(a,k)\ne(-1,0)$ (2a), or $-\kappa<a<-1$ and $|a|^{-1/(1-\alpha)}>1-\gamma e^{-r\tau}$ (2b): $y^*_a(q)=I_2(q)$ for $0<q\le m_2$ and $0$ for $q>m_2$, where $I_2(q)$ is the solution of $\alpha[(y-\gamma)^{\alpha-1}+ay^{\alpha-1}]=q$ on $y\ge c_3\gamma$, with values in $[c_3\gamma,\infty)$ (2a) or $[c_3\gamma,\gamma/(1-|a|^{-1/(1-\alpha)}))$ (2b);
--   3. if $a\le-\kappa$: $y^*_a\equiv0$;
--   4. if $-\kappa<a<-1$ and $|a|^{-1/(1-\alpha)}\le1-\gamma e^{-r\tau}$: $y^*_a\equiv\gamma/(1-|a|^{-1/(1-\alpha)})$.
--
--   Here $m_1>0$, $m_2>0$. In Cases 1, 2a and 2b, $\lambda^*$ is the unique $\lambda>0$ with $E[Z_\tau y^*_a(\lambda Z_\tau)]=1$. In Cases 1–3, $y^*_a$ is a maximizer selection of $q\mapsto\arg\max_{y\ge0}(\bar G_a(y)-qy)$.
--
--   This solves the one-period problem whose value defines $\Phi$; Theorem 1 applies it period by period at $a=A^*$.
--
--   **Formalization Note** "The optimizer is given by $Y^*$" is stated as: $Y^*$ is feasible, $G_a(Y^*)$ is integrable and $E[G_a(Y^*)]=F(a)$. The constants are identified by their defining relations in Lemma 2; $I_1$, $I_2$ by "lies in the range, solves the equation, and is the only solution there". $E[Z_\tau y(\lambda Z_\tau)]$ is the Lebesgue integral of a nonnegative variable.
--
--   Differences from the source:
--   - correction: Cases 1 and 2 for every γ ≥ 0 → Cases 1 and 2 for γ > 0 (Cases 3 and 4 for every γ ≥ 0); reason: at γ = 0, a = 1, k = 0: Case 1 asserts I1 : (m1, ∞) → (0, c1·0) = ∅, impossible, and m1, m2 = γ^{α−1}(…) are undefined (at γ = 0, −1 < a ≤ 0 the optimizer is the Merton one, not 0 for q > m2); Cases 3 and 4 hold at γ = 0 as printed; the paper treats γ = 0 in Corollary 1 and Theorem 1 keeps γ = 0
--   - correction: Case 2 for all −1 ≤ a ≤ 0 → Case 2 for −1 ≤ a ≤ 0 with (a, k) ≠ (−1, 0); reason: at k = 0, a = −1, γ > 0, equation (22) has no root c3 > 1 (Lemma 2), so Case 2(a) is undefined; Case 3 (y* ≡ 0) holds there and is kept
--   - reading: 'the optimizer to problem (14) is given by Y* = y*_a(λ*Z_τ)' → Y* is feasible, G_a(Y*) is integrable and E[G_a(Y*)] = F(a); reason: the proof shows that Y* attains the supremum; uniqueness of the optimizer is not claimed (at a = −κ there are two)
--   - generalization: statement of Proposition 3 → also: y*_a is a maximizer selection for Ḡ_a in Cases 1–3; reason: the proof defines y*_a = y*_{Ḡ_a} as this argmax (p.38); dropping the clause gives the printed statement
--   - encoding: I1, I2 'the solution to the equation on …'; λ* with E[Z_τ y*_a(λZ_τ)] = 1 → range + equation + uniqueness in the range; lower Lebesgue integral; reason: the same functions; the integrand is nonnegative, so the Lebesgue integral is the expectation
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Proposition 3, p.37, and its proof, pp.37–39

import Mathlib
import Definitions.Def_PeriodicEval_Auxiliary
import Definitions.Def_PeriodicEval_Concavify

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Proposition 3 (corrected), SSRN 3971852 (June 20, 2023), p.37: the optimizer of problem (14)
is `Y* = y*_a(λ*Z_τ)`, where, with the constants `c₁, c₂, c₃, m₁, m₂` of Lemma 2,
1. if `a > 0`: `y*_a(q) = I₂(q)` for `0 < q ≤ m₁` and `I₁(q)` for `q > m₁`, where `I₁(q)` is the
   solution of `α[k(γ − y)^{α−1} + a y^{α−1}] = q` on `(0, c₁γ)` and `I₂(q)` the solution of
   `α[(y − γ)^{α−1} + a y^{α−1}] = q` on `[c₂γ, ∞)`;
2. if `−1 ≤ a ≤ 0` (2a), or `−κ < a < −1` and `|a|^{−1/(1−α)} > 1 − γe^{−rτ}` (2b):
   `y*_a(q) = I₂(q)` for `0 < q ≤ m₂` and `0` for `q > m₂`, where `I₂(q)` is the solution of
   `α[(y − γ)^{α−1} + a y^{α−1}] = q` on `y ≥ c₃γ`, with values in `[c₃γ, ∞)` (2a) or
   `[c₃γ, γ/(1 − |a|^{−1/(1−α)}))` (2b);
3. if `a ≤ −κ`: `y*_a ≡ 0`;
4. if `−κ < a < −1` and `|a|^{−1/(1−α)} ≤ 1 − γe^{−rτ}`: `y*_a ≡ γ/(1 − |a|^{−1/(1−α)})`.
Here `m₁ > 0`, `m₂ > 0`, `0 < c₁ < 1 < c₂`, `c₃ > 1`; in Cases 1, 2a and 2b, `λ*` is the unique
`λ > 0` with `E[Z_τ y*_a(λZ_τ)] = 1`. In Cases 1–3, `y*_a` is a maximizer selection of
`q ↦ arg max_{y ≥ 0}(Ḡ_a(y) − qy)` (p.38, "Write `y*_a(·) = y*_{Ḡ_a}(·)`").

**Formalization Note** Corrections: `γ > 0` is assumed in Cases 1 and 2 (at `γ = 0`, `I₁`
would map into `(0, c₁·0) = ∅` and `m₁, m₂` are undefined; the paper treats `γ = 0` in
Corollary 1; Cases 3 and 4 hold as printed at `γ = 0` and are stated for every `γ ≥ 0`), and
Case 2 excludes `(a, k) = (−1, 0)` (there (22) has no root; Case 3 applies). The constants are
identified by the defining relations of Lemma 2 ((20), (22) in their ranges), which determine
them uniquely; `I₁`, `I₂` are encoded by "`y q` lies in the range and solves the equation, and
is the only solution there". "The optimizer is given by" is existence: `Y*` is feasible and
attains `F(a)`. `E[Z_τ y(λZ_τ)]` is a lower Lebesgue integral of a nonnegative variable. -/
theorem proposition_3 (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (a : ℝ) :
    -- Case 1 (corrected: γ > 0)
    (0 < p.γ → 0 < a →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < 1 / (1 + (p.k / a) ^ (1 / (2 - p.α))) ∧ 1 < c₂ ∧
        ((c₂ - 1) ^ p.α + a * c₂ ^ p.α + p.k * (1 - c₁) ^ p.α - a * c₁ ^ p.α) / (c₂ - c₁) =
            p.α * ((c₂ - 1) ^ (p.α - 1) + a * c₂ ^ (p.α - 1)) ∧
        p.α * ((c₂ - 1) ^ (p.α - 1) + a * c₂ ^ (p.α - 1)) =
            p.α * (p.k * (1 - c₁) ^ (p.α - 1) + a * c₁ ^ (p.α - 1)) ∧
        let m₁ := p.γ ^ (p.α - 1) *
          (((c₂ - 1) ^ p.α + a * c₂ ^ p.α + p.k * (1 - c₁) ^ p.α - a * c₁ ^ p.α) / (c₂ - c₁))
        0 < m₁ ∧
        ∃ y : ℝ → ℝ,
          (∀ q : ℝ, m₁ < q →
            (0 < y q ∧ y q < c₁ * p.γ ∧
              p.α * (p.k * (p.γ - y q) ^ (p.α - 1) + a * y q ^ (p.α - 1)) = q) ∧
            ∀ z : ℝ, 0 < z → z < c₁ * p.γ →
              p.α * (p.k * (p.γ - z) ^ (p.α - 1) + a * z ^ (p.α - 1)) = q → z = y q) ∧
          (∀ q : ℝ, 0 < q → q ≤ m₁ →
            (c₂ * p.γ ≤ y q ∧ p.α * ((y q - p.γ) ^ (p.α - 1) + a * y q ^ (p.α - 1)) = q) ∧
            ∀ z : ℝ, c₂ * p.γ ≤ z →
              p.α * ((z - p.γ) ^ (p.α - 1) + a * z ^ (p.α - 1)) = q → z = y q) ∧
          IsArgmaxSelection (concaveMajorant (G p a)) y ∧
          ∃ lam : ℝ, 0 < lam ∧
            (∀ l : ℝ, 0 < l →
              (∫⁻ ω, ENNReal.ofReal (Z p B p.τ.toNNReal ω * y (l * Z p B p.τ.toNNReal ω)) ∂P = 1
                ↔ l = lam)) ∧
            IsOptimal p P ℱ B a (fun ω => y (lam * Z p B p.τ.toNNReal ω))) ∧
    -- Case 2 (corrected: γ > 0; 2a: (a, k) ≠ (−1, 0); 2b)
    (0 < p.γ → (-1 ≤ a ∧ a ≤ 0 ∧ ¬(a = -1 ∧ p.k = 0)) ∨
        (-p.κ < a ∧ a < -1 ∧ 1 - p.γ * Real.exp (-(p.r * p.τ)) < |a| ^ (-1 / (1 - p.α))) →
      ∃ c₃ : ℝ, 1 < c₃ ∧ (a < -1 → c₃ < 1 / (1 - |a| ^ (-1 / (1 - p.α)))) ∧
        ((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃ =
          p.α * ((c₃ - 1) ^ (p.α - 1) + a * c₃ ^ (p.α - 1)) ∧
        let m₂ := p.γ ^ (p.α - 1) * (((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃)
        0 < m₂ ∧
        ∃ y : ℝ → ℝ,
          (∀ q : ℝ, m₂ < q → y q = 0) ∧
          (∀ q : ℝ, 0 < q → q ≤ m₂ →
            (c₃ * p.γ ≤ y q ∧ (a < -1 → y q < p.ymax a) ∧
              p.α * ((y q - p.γ) ^ (p.α - 1) + a * y q ^ (p.α - 1)) = q) ∧
            ∀ z : ℝ, c₃ * p.γ ≤ z →
              p.α * ((z - p.γ) ^ (p.α - 1) + a * z ^ (p.α - 1)) = q → z = y q) ∧
          IsArgmaxSelection (concaveMajorant (G p a)) y ∧
          ∃ lam : ℝ, 0 < lam ∧
            (∀ l : ℝ, 0 < l →
              (∫⁻ ω, ENNReal.ofReal (Z p B p.τ.toNNReal ω * y (l * Z p B p.τ.toNNReal ω)) ∂P = 1
                ↔ l = lam)) ∧
            IsOptimal p P ℱ B a (fun ω => y (lam * Z p B p.τ.toNNReal ω))) ∧
    -- Case 3
    (a ≤ -p.κ →
      IsArgmaxSelection (concaveMajorant (G p a)) (fun _ => 0) ∧
        IsOptimal p P ℱ B a (fun _ => 0)) ∧
    -- Case 4
    (-p.κ < a ∧ a < -1 ∧ |a| ^ (-1 / (1 - p.α)) ≤ 1 - p.γ * Real.exp (-(p.r * p.τ)) →
      IsOptimal p P ℱ B a (fun _ => p.ymax a)) := by sorry

end PeriodicEval
