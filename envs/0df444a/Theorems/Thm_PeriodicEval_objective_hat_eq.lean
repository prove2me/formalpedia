-- Prove2me | Theorems.Thm_PeriodicEval_objective_hat_eq
-- name    : PeriodicEval.objective_hat_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:08.569004+00:00
-- url     : https://prove2.me/theorems/e8533828-01fc-44ad-8d11-15f8c4a88622
-- title:
--   Proof of Theorem 1, p.44 — $\hat M$ is a martingale and the candidate attains $A^*x^\alpha$
-- statement:
--   Under the standing assumptions, let $x>0$, $A^*$ the fixed point of $\Phi$, $y$ a maximizer selection for $\bar G_{A^*}$, and $\lambda>0$ with $E[Z_\tau y(\lambda Z_\tau)]=1$ whenever $A^*>-\kappa$ (Cases 1, 2a, 2b). Let $H_n:=x\prod_{i=1}^ny\big(\lambda Z_{T_i}/Z_{T_{i-1}}\big)$, i.e. $H_n=H_{n-1}y(\lambda Z_{T_n}/Z_{T_{n-1}})$, $H_0=x$. For every $\hat X\in\mathcal A_0(x)$ with $\hat X_{T_n}=H_n$ for all $n$, the process
--
--   $$\hat M_n:=\sum_{i=1}^ne^{-\beta T_i}U(\hat X_{T_i}-\gamma\hat X_{T_{i-1}})+A^*e^{-\beta T_n}\hat X^\alpha_{T_n}$$
--
--   is a martingale for $\mathcal G_n=\mathcal F_{T_n}$, and
--
--   $$E\Big[\sum_{i=1}^\infty e^{-\beta T_i}U(\hat X_{T_i}-\gamma\hat X_{T_{i-1}})\Big]=A^*x^\alpha.$$
--
--   This is the lower half of $V(x)=A^*x^\alpha$ and shows that $\hat X$ is optimal.
--
--   **Formalization Note** The martingale property is stated as measurability, integrability and $E[\hat M_{n+1}\mid\mathcal F_{T_n}]=\hat M_n$.
--
--   Differences from the source:
--   - generalization: y*_{A*} of Proposition 3 → every maximizer selection y for Ḡ_{A*}; reason: the paper's function is such a selection (p.38); selections differ only at one value of q, a null event for λZ
--   - encoding: H_n := H_{n−1} y*(λ*Z_{T_n}/Z_{T_{n−1}}), λ* in Cases 1, 2a, 2b → the unrolled product; any λ > 0 in Case 3; reason: the same sequence; in Case 3 y ≡ 0 on (0, ∞), so λ does not matter
--   - encoding: M̂ is a {G_n}-martingale → measurability, integrability and the one-step identity; reason: equivalent in discrete time by the tower property
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.44

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary
import Definitions.Def_PeriodicEval_Concavify

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- The candidate optimizer attains `A*x^α`, SSRN 3971852 (June 20, 2023), proof of Theorem 1,
p.44. Let `A*` be the fixed point of `Φ`, `y*_{A*}` a maximizer selection for `Ḡ_{A*}`, `λ* > 0`
with `E[Z_τ y*_{A*}(λ*Z_τ)] = 1` in Cases 1, 2a, 2b (`A* > −κ`), and
`H_n := H_{n−1} y*_{A*}(λ*Z_{T_n}/Z_{T_{n−1}})`, `H_0 := x > 0`. For every `X̂ ∈ A_0(x)` with
`X̂_{T_n} = H_n` for all `n`, the process
`M̂_n := ∑_{i=1}^n e^{−βT_i}U(X̂_{T_i} − γX̂_{T_{i−1}}) + A*e^{−βT_n}X̂^α_{T_n}`
is a `{𝒢_n}`-martingale, `𝒢_n := ℱ_{T_n}`, and
`E[∑_{i=1}^∞ e^{−βT_i}U(X̂_{T_i} − γX̂_{T_{i−1}})] = A*x^α`.

**Formalization Note** `y*_{A*}` is any maximizer selection of `q ↦ arg max_{y≥0}(Ḡ_{A*}(y) − qy)`
(p.38); the paper's explicit choice (Proposition 3) is one of them. The martingale property is
stated as measurability, integrability and the one-step identity
`E[M̂_{n+1} | ℱ_{T_n}] = M̂_n`. Equalities `X̂_{T_n} = H_n` are almost sure. -/
theorem objective_hat_eq (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (A : ℝ)
    (hA : Φ p P ℱ B A = (A : EReal)) (y : ℝ → ℝ)
    (hy : IsArgmaxSelection (concaveMajorant (G p A)) y) (lam : ℝ) (hlam : 0 < lam)
    (hlam1 : -p.κ < A →
      ∫⁻ ω, ENNReal.ofReal (Z p B p.τ.toNNReal ω * y (lam * Z p B p.τ.toNNReal ω)) ∂P = 1)
    (Xh : ℝ≥0 → Ω → ℝ) (hXh : Xh ∈ admissible p P ℱ B 0 x)
    (hXhH : ∀ n : ℕ, Xh (p.T n) =ᵐ[P] fun ω =>
      x * ∏ i ∈ Finset.range n, y (lam * (Z p B (p.T (i + 1)) ω / Z p B (p.T i) ω))) :
    let Mh : ℕ → Ω → ℝ := fun n ω =>
      (∑ i ∈ Finset.range n, Real.exp (-(p.β * (p.T (i + 1) : ℝ))) *
          U p (Xh (p.T (i + 1)) ω - p.γ * Xh (p.T i) ω)) +
        A * Real.exp (-(p.β * (p.T n : ℝ))) * Xh (p.T n) ω ^ p.α
    (∀ n : ℕ, StronglyMeasurable[ℱ (p.T n)] (Mh n)) ∧
    (∀ n : ℕ, Integrable (Mh n) P) ∧
    (∀ n : ℕ, P[Mh (n + 1) | ℱ (p.T n)] =ᵐ[P] Mh n) ∧
    objective p P Xh = A * x ^ p.α := by sorry

end PeriodicEval
