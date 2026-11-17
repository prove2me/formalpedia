-- Prove2me | Theorems.Thm_ThinShellSampling_Supplement_theorem_1_5
-- name    : ThinShellSampling.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:39:53.316632+00:00
-- url     : https://prove2.me/theorems/66141e2a-75dd-44b9-a503-8bd9206c4a58
-- title:
--   Theorem 1.5 — thin-shell Gaussian cooling: $\mathsf R_q$ warm start for a convex body in $\widetilde O(q^{1/2}n^2\min\{RL^{1/2},R^{3/2}\Lambda^{1/4}\})$ queries
-- statement:
--   There is a randomized membership-oracle algorithm $\mathcal A$, which receives the dimension $n$, a Rényi order $q$ and a number $\bar{\mathsf V}$ and restarts independent attempts until one succeeds, with the following property. For every $C_1>0$ there are constants $C>0$ and $k\in\mathbb N$ such that, for every $n\ge1$, every convex body $\mathcal K\subset\mathbb R^n$ with $B(0,1)\subset\mathcal K$, with $\pi$ uniform on $\mathcal K$, every $q\ge1$ and every $\bar{\mathsf V}$ with
--
--   $$
--   \sup_{\sigma^2>0}\operatorname{Var}_{\pi_{\sigma^2}}(\|X\|^2)\le\bar{\mathsf V}\le C_1\big(R^2L\wedge R^3\sqrt\Lambda\big),
--   $$
--
--   the run of $\mathcal A(n,q,\bar{\mathsf V})$ against the membership oracle of $\mathcal K$ halts almost surely, its output law $\nu$ satisfies
--
--   $$
--   \mathsf R_q(\nu\,\|\,\pi)\le1,
--   $$
--
--   and its expected number of membership queries is at most $C\,B\log^k(2+B)$ both for $B=q^{1/2}n^2\bar{\mathsf V}^{1/2}$ and for $B=q^{1/2}n^2\min\{RL^{1/2},R^{3/2}\Lambda^{1/4}\}$.
--
--   Here $\pi_{\sigma^2}(dx)\propto e^{-\|x\|^2/(2\sigma^2)}\pi(dx)$ is the Gaussian tilt, $R^2=\mathbb E_\pi\|X\|^2$, $L=\|\mathbb E_\pi[XX^{\mathsf T}]\|_{\mathrm{op}}$ and $\Lambda=\|\operatorname{cov}\pi\|_{\mathrm{op}}$. For nearly isotropic $\pi$ the bound is $\widetilde O(q^{1/2}n^{2.5})$.
--
--   This is the cold-start warm-start generator for uniform sampling (thin-shell Gaussian cooling, Algorithm 5.5); its output feeds Theorem 1.1.
--
--   **Formalization Note** The algorithm is an attempt program in the published oracle model `Prog` (queries cost 1, uniform samples and arithmetic cost 0) wrapped by the restart-until-success algorithm `restartLaw`; it is run against the indicator potential of $\mathcal K$, whose evaluation oracle is the membership oracle. At $q=1$ the divergence is KL.
--
--   Differences from the source:
--
--   - reading: "Algorithm 5.5 outputs a law ν …" → there exists an attempt program A(n, q, V̄), fixed before C₁ and before every instance, whose restart-until-success wrapper has the stated properties; reason: Algorithm 5.5 is specified only up to Õ(·) and Θ(·) (N_{i+1}, q_min), as Algorithm 6.6 for the published goal; "If a cap is hit, return to Step 1 and start an independent annealing attempt" is the restart wrapper
--   - reading: input V = O(R²L ∧ R³Λ^{1/2}), the thin-shell bound of Corollary 5.3 → sup_{σ²>0} Var_{π_{σ²}}(‖X‖²) ≤ V̄ ≤ C₁·min(R²L, R³√Λ) for an arbitrary C₁ > 0, the constants C, k depending only on C₁; reason: O(·) is a universal constant (§1.3, p.12); the program inputs are n, q and V̄ only (Algorithm 5.5 has no truncation radius)
--   - encoding: V := sup_{s≥0} Var_{ν_s}(‖X‖²) (Corollary 5.3) → supremum over σ² > 0 of evariance(‖·‖²) under gaussTilt π σ² (s = 1/(2σ²)); reason: for a convex body s ↦ Var_{ν_s}(‖X‖²) is continuous at s = 0 (bounded support), so the two suprema coincide; Theorem 1.4 is printed with sup_{t>0}
--   - reading: Õ(q^{1/2}n²V^{1/2}) = Õ(q^{1/2}n² min{RL^{1/2}, R^{3/2}Λ^{1/4}}) expected membership queries → expected total queries ≤ C·B·log(2 + B)^k both for B = q^{1/2}n²V̄^{1/2} and for B = q^{1/2}n² min{R L^{1/2}, R^{3/2}Λ^{1/4}}; reason: §1.3, p.12: Õ(b) = O(b polylog b); both printed bounds are kept
--   - reading: "outputs a law ν satisfying R_q(ν ∥ π) ≤ 1 for q ≥ 1" → the restart run halts almost surely, its output map and total query count are a.e.-measurable, and renyi q (law) π ≤ 1 for every real q ≥ 1; reason: a law exists only for an a.s.-halting run with a measurable output
--   - reading: "When π is nearly isotropic (i.e., cov π ≈ Iₙ), the total complexity is Õ(q^{1/2}n^{2.5})" → not a separate clause; reason: informal (≈); it is the bound at R² ≍ n, L ≍ Λ ≍ 1
--   - encoding: convex body K ⊂ ℝⁿ with B(0, 1) ⊂ K, π uniform on K, membership oracle → K compact and convex with the open unit ball ⊆ K; π = piOf (indicatorPot K); the oracle is the evaluation oracle of indicatorPot K; reason: a query answers x ∈ K; for closed K the open and closed unit-ball readings agree
--   - encoding: R_q for q ≥ 1 → renyi q in [0, ∞], KL at q = 1, ∞ off absolute continuity; reason: q = 1 is KL = lim_{q↓1} R_q (footnote 1, p.1)
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.5, p.4 (PDF p.6); Algorithm 5.5, p.32 (PDF p.34); Corollary 5.3, p.31 (PDF p.33); proof pp.32–34 (PDF pp.34–36)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat
import Definitions.Def_ThinShellSampling_piOf
import Definitions.Def_ThinShellSampling_Prog
import Definitions.Def_ThinShellSampling_Supplement_restartLaw
import Definitions.Def_ThinShellSampling_Supplement_indicatorPot

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.5 (Faster warm start for uniform sampling).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.5, p.4 (PDF p.6): "Let `K ⊂ ℝⁿ` be a convex body with `B(0, 1) ⊂ K` and `π`
uniform on `K`. Algorithm 5.5 outputs a law `ν` satisfying `R_q(ν ‖ π) ≤ 1` for `q ≥ 1`, using
`Õ(q^{1/2}n²V^{1/2}) = Õ(q^{1/2}n² min{RL^{1/2}, R^{3/2}Λ^{1/4}})` expected membership queries."
Algorithm 5.5, p.32 (PDF p.34), takes as input "membership oracle for `K` with `B(0, 1) ⊂ K`,
Rényi-order `q`, and `V = O(R²L ∧ R³Λ^{1/2})`", the thin-shell bound of Corollary 5.3
(`V := sup_{s≥0} Var_{ν_s}(‖X‖²)`, p.31 = PDF p.33). Proof pp.32–34 (PDF pp.34–36).

**Formalization Note.**
* **Algorithm.** Algorithm 5.5 is specified only up to `Õ`, `Θ` and hidden constants (`N_{i+1}`,
  `q_min`), so the statement is the complexity claim: there **exists** an attempt program `A n q V̄`
  (fixed before every constant and instance; inputs the dimension, the order and the thin-shell bound
  only) whose restart-until-success wrapper (`restartLaw`, `restartExpQueries`) has the stated
  properties. The program reaches `K` only through membership queries (`Prog` run against
  `indicatorPot K`).
* **Input range.** `sup_{σ²>0} Var_{π_{σ²}}(‖X‖²) ≤ V̄ ≤ C₁·(R²L ∧ R³√Λ)` for an arbitrary
  `C₁ > 0`; `C, k` may depend on `C₁` only. For a convex body the supremum over `σ² > 0` equals the
  supremum over `s ≥ 0` of Corollary 5.3 (the variance is continuous at `s = 0`, the support being
  bounded).
* **`Õ`.** `≤ C·B·log(2 + B)^k` with universal `C, k` (§1.3, p.12), asserted for both printed
  expressions `B = q^{1/2}n²V̄^{1/2}` and `B = q^{1/2}n² min{R L^{1/2}, R^{3/2}Λ^{1/4}}`.
* **Output.** The restart run halts almost surely, its output map and total query count are
  a.e.-measurable, and `R_q(law ‖ π) ≤ 1` for every real `q ≥ 1` (KL at `q = 1`).
* `π = piOf (indicatorPot K)` (uniform on `K`); `R² = E_π‖X‖²`, `L = ‖E_π[XXᵀ]‖_op`,
  `Λ = ‖cov π‖_op`. -/
theorem theorem_1_5 :
    ∃ A : (n : ℕ) → ℝ → ℝ → Prog n (Option (EuclideanSpace ℝ (Fin n))),
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K → Convex ℝ K → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K →
    ∀ q : ℝ, 1 ≤ q → ∀ Vbar : ℝ,
      (⨆ σ2 : ℝ, ⨆ (_ : 0 < σ2),
          evariance (fun x => ‖x‖ ^ 2) (gaussTilt (piOf (indicatorPot K)) σ2)) ≤
        ENNReal.ofReal Vbar →
      Vbar ≤ C₁ * min (Rrad (indicatorPot K) ^ 2 * Lmom (piOf (indicatorPot K)))
        (Rrad (indicatorPot K) ^ 3 * Real.sqrt (Lam (piOf (indicatorPot K)))) →
      let V := indicatorPot K
      let p := A n q Vbar
      let R := Rrad V
      let L := Lmom (piOf V)
      let Λ := Lam (piOf V)
      let B₁ : ℝ := Real.sqrt q * (n : ℝ) ^ 2 * Real.sqrt Vbar
      let B₂ : ℝ := Real.sqrt q * (n : ℝ) ^ 2 *
        min (R * Real.sqrt L) (R ^ (3 / 2 : ℝ) * Λ ^ (1 / 4 : ℝ))
      (∀ᵐ ws ∂restartMeasure, RestartHalts V p ws) ∧
      AEMeasurable (restartOutput 0 V p) restartMeasure ∧
      AEMeasurable (restartQueries V p) restartMeasure ∧
      renyi q (restartLaw V p) (piOf V) ≤ 1 ∧
      restartExpQueries V p ≤ ENNReal.ofReal (C * B₁ * Real.log (2 + B₁) ^ k) ∧
      restartExpQueries V p ≤ ENNReal.ofReal (C * B₂ * Real.log (2 + B₂) ^ k) := by sorry

end ThinShellSampling.Supplement
