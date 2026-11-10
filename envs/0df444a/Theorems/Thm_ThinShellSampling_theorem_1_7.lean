-- Prove2me | Theorems.Thm_ThinShellSampling_theorem_1_7
-- name    : ThinShellSampling.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:59.929821+00:00
-- url     : https://prove2.me/theorems/da595d7e-a65b-401d-b712-0f78416dfd17
-- title:
--   Theorem 1.7 — Rényi warm start for logconcave sampling in $\widetilde O(n^{2.5}+q^{1/2}n^2\min\{RL^{1/2},R^{3/2}\Lambda^{1/4}\})$ queries
-- statement:
--   There is a randomized evaluation-oracle algorithm $\mathcal A$, which receives the dimension $n$, a Rényi order $q$, a number $\bar{\mathcal V}$ and the radius $R$, and accesses $V$ only through evaluation queries, with the following property. For every $C_1>0$ there are constants $C,k$ such that for every $n\ge1$, every convex $V:\mathbb R^n\to\mathbb R\cup\{\infty\}$ with $B(0,1)\subseteq L_g=\{V-\min V\le10n\}$ and $\int e^{-V}<\infty$, every $q\ge1$, and every $\bar{\mathcal V}$ with
--
--   $$
--   \sup_{\sigma^2>0}\operatorname{Var}_{\bar\pi_{\sigma^2}}(\|X\|^2)\le\bar{\mathcal V}\le C_1\big(R^2L\wedge R^3\sqrt\Lambda\big),
--   $$
--
--   the run of $\mathcal A(n,q,\bar{\mathcal V},R)$ against $V$ halts almost surely, its output law $\nu$ satisfies
--
--   $$
--   \mathsf R_q(\nu\,\|\,\pi)\le2,
--   $$
--
--   and its expected number of evaluation queries is at most $C\,B\log^k(2+B)$, where
--
--   $$
--   B=n^{5/2}+q^{1/2}n^2\min\{RL^{1/2},\,R^{3/2}\Lambda^{1/4}\}.
--   $$
--
--   Here $\pi\propto e^{-V}$, $R^2=\mathbb E_\pi\|X\|^2$, $L=\|\mathbb E_\pi[XX^{\mathsf T}]\|_{\mathrm{op}}$, $\Lambda=\|\operatorname{cov}\pi\|_{\mathrm{op}}$, and $\bar\pi_{\sigma^2}$ is the Gaussian tilt of the $X$-marginal $\bar\pi$ of the truncated exponential lift of §6.2. For nearly isotropic $\pi$ ($R^2\asymp n$, $L\asymp\Lambda\asymp1$) the bound is $\widetilde O(q^{1/2}n^{2.5})$.
--
--   This is the cold-start complexity of zeroth-order sampling from an arbitrary logconcave distribution: it produces an $\mathsf R_q$-warm start, from which the warm-start sampler of Theorem 1.6 reaches any accuracy at no loss in the Rényi order.
--
--   **Formalization Note** The algorithm is a program in the oracle model `Prog` (queries cost 1, uniform samples cost 0, arithmetic is free); the output map and the query count are asserted to be a.e.-measurable in the random stream. At $q=1$ the divergence is KL.
--
--   Differences from the source:
--
--   - reading: "Algorithm 6.6 outputs a law ν …" → there exists an oracle program A(n, q, V̄, R), fixed before C₁ and before every instance; reason: Algorithm 6.6 is specified only up to Õ(·), Θ̃(·) and "a sufficiently small constant c", so the claim is the complexity statement; the milestones keep the paper's own objects
--   - reading: inputs of Algorithm 6.6: the oracle, q ≥ 1, V̄ and c → program inputs n, q, V̄ and R; V only through queries; reason: Step 1 uses the truncation radius D = 1 ∨ Rℓ of §6.2, which needs R; c is a constant of the program
--   - reading: sup_{σ²>0} Var_{π̄_{σ²}}(‖X‖²) ≤ V ≲ R²L ∧ R³√Λ → the same with ≲ read as ≤ C₁·(…) for an arbitrary C₁ > 0, the constants C, k depending only on C₁; reason: ≲ is a universal constant (§1.3, p.12)
--   - reading: Õ(n^{2.5} + q^{1/2}n² min{RL^{1/2}, R^{3/2}Λ^{1/4}}) → C·B·log(2 + B)^k with B the displayed expression; reason: §1.3, p.12: a = Õ(b) means a = O(b polylog b); 2 + B keeps the logarithm positive
--   - reading: "outputs a law ν" → the run halts almost surely and its output map and query count are a.e.-measurable; reason: a law of the output exists only for an a.s. terminating run with a measurable output
--   - reading: "When π is nearly isotropic (i.e., cov π ≈ Iₙ), the total complexity is Õ(q^{1/2}n^{2.5})" → not a separate clause; reason: informal (≈); it is the bound at R² ≍ n, L ≍ Λ ≍ 1
--   - reading: π ∝ e^{−V} a distribution → hypothesis ∫ e^{−V} < ∞; B(0, 1) the open ball; reason: normalizability is implicit in "π ∝ e^{−V}"; the open ball is the weaker hypothesis
--   - encoding: V : ℝⁿ → ℝ ∪ {∞} convex, min V, evaluation oracle → V : ℝⁿ → WithTop ℝ with convex domain and convex on it; min V the infimum over the domain; programs with query (cost 1) and Uniform[0, 1] sample (cost 0) instructions run on an i.i.d. uniform stream; reason: Lean representation of the same objects and of query complexity
--   - encoding: R_q for q ≥ 1 → renyi q in [0, ∞], KL at q = 1, ∞ off absolute continuity; reason: q = 1 is KL = lim_{q↓1} R_q (footnote 1, p.1)
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.7, p.5 (PDF p.7); Algorithm 6.6, p.40 (PDF p.42); proof pp.40–41 (PDF pp.42–43)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat
import Definitions.Def_ThinShellSampling_piOf
import Definitions.Def_ThinShellSampling_muAnneal
import Definitions.Def_ThinShellSampling_Prog

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.7 (Faster warm start for logconcave sampling).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.7, p.5 (PDF p.7): "Let `V : ℝⁿ → ℝ ∪ {∞}` be a convex function, and suppose that
`π ∝ e^{−V}` satisfies `B(0, 1) ⊆ L_g`. Given access to an evaluation oracle for `V`, Algorithm 6.6 outputs
a law `ν` satisfying `R_q(ν ‖ π) ≤ 2` for `q ≥ 1`, using the expected number of evaluation queries bounded
by `Õ(n^{2.5} + q^{1/2}n² min{RL^{1/2}, R^{3/2}Λ^{1/4}})`." Algorithm 6.6, p.40 (PDF p.42), takes as input
"a target order `q ≥ 1`, `sup_{σ²>0} Var_{π̄_{σ²}}(‖X‖²) ≤ V ≲ R²L ∧ R³√Λ`".

**Formalization Note.**
* **Algorithm.** Algorithm 6.6 is specified only up to `Õ`, `Θ̃` and "a sufficiently small constant", so
  the statement is the complexity claim: there **exists** an oracle program `A n q V̄ R` (fixed before
  every constant and every instance) whose inputs are the dimension `n`, the order `q`, the thin-shell
  bound `V̄` (an input of Algorithm 6.6) and `R` (the truncation radius `D = 1 ∨ Rℓ` of §6.2 uses it). The
  program reaches `V` only through evaluation queries (`Prog`).
* **Input range.** `sup_{σ²>0} Var_{π̄_{σ²}}(‖X‖²) ≤ V̄ ≤ C₁·(R²L ∧ R³√Λ)` for an arbitrary `C₁ > 0`; the
  constants `C, k` may depend on `C₁` only. `π̄` is the `X`-marginal of the truncated lift built from `V`
  and `R` (§6.2), and `π̄_{σ²}` its Gaussian tilt.
* **`Õ`.** `a = Õ(b)` means `a ≤ C·b·log(2 + b)^k` with universal `C, k` (§1.3, p.12: "`a = O(b polylog b)`").
* **Output.** The run halts almost surely; its output map and query count are a.e.-measurable;
  `R_q(law ‖ π) ≤ 2` for every real `q ≥ 1` (`q = 1` is the KL divergence); and the expected number of
  queries is at most `C·B·log(2 + B)^k` with `B = n^{5/2} + q^{1/2}n² min{R L^{1/2}, R^{3/2}Λ^{1/4}}`.
* `R, L, Λ` are those of `π`: `R² = E_π‖X‖²`, `L = ‖E_π[XXᵀ]‖_op`, `Λ = ‖cov π‖_op`. -/
theorem theorem_1_7 :
    ∃ A : (n : ℕ) → ℝ → ℝ → ℝ → Prog n (EuclideanSpace ℝ (Fin n)),
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ V : EuclideanSpace ℝ (Fin n) → WithTop ℝ, IsStandardPotential V →
    ∀ q : ℝ, 1 ≤ q → ∀ Vbar : ℝ,
      (⨆ σ2 : ℝ, ⨆ (_ : 0 < σ2),
          evariance (fun x => ‖x‖ ^ 2) (gaussTilt (piBar V (Rrad V)) σ2)) ≤ ENNReal.ofReal Vbar →
      Vbar ≤ C₁ * min (Rrad V ^ 2 * Lmom (piOf V)) (Rrad V ^ 3 * Real.sqrt (Lam (piOf V))) →
      let p := A n q Vbar (Rrad V)
      let B : ℝ := (n : ℝ) ^ (5 / 2 : ℝ) + Real.sqrt q * (n : ℝ) ^ 2 *
        min (Rrad V * Real.sqrt (Lmom (piOf V)))
          (Rrad V ^ (3 / 2 : ℝ) * Lam (piOf V) ^ (1 / 4 : ℝ))
      (∀ᵐ ω ∂streamMeasure, Halts V p ω) ∧
      AEMeasurable (output 0 V p) streamMeasure ∧
      AEMeasurable (queryCount V p) streamMeasure ∧
      renyi q (lawOf V p) (piOf V) ≤ 2 ∧
      expQueries V p ≤ ENNReal.ofReal (C * B * Real.log (2 + B) ^ k) := by sorry

end ThinShellSampling
