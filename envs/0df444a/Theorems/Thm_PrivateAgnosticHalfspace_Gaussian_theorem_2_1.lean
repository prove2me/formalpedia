-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_theorem_2_1
-- name    : PrivateAgnosticHalfspace.Gaussian.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:31.649733+00:00
-- url     : https://prove2.me/theorems/913a6178-373d-4dc9-8296-f1899b19b16c
-- title:
--   Theorem 2.1 — efficient private Gaussian agnostic halfspace learning
-- statement:
--   There are universal constants $C,A\ge1$, $0<c\le1/4$ and $C_{\rm dim}\ge2(C+1)^2/c$, a uniform sample-only private optimizer and fixed costed programs implementing that optimizer and Algorithm 1. They are chosen before all learning instances and before the unknown population law. The optimizer's normalization, measurability, replacement privacy, expected empirical excess-loss bound and arithmetic implementation are conclusions, not assumptions.
--
--   For every $\alpha,\beta,\varepsilon,\delta\in(0,1/2]$ and integer $d\ge C_{\rm dim}\alpha^{-5}$, put $p=\lceil C\alpha^{-2}\rceil$, $D=D_p=\binom{d+p}{p}$, $T=2\sqrt D$, $k=\lceil\log_2(2/\beta)\rceil$ and $M=\lceil C/\alpha\rceil$. Let $n_0\ge2$ be the least integer with
--   $$
--   C\left(\frac{T\sqrt{D\log(1/\delta)}}{\varepsilon n_0}+\sqrt{D/n_0}\right)\le c\alpha,
--   \qquad m=\left\lceil C\left(\alpha^{-2}+(\varepsilon\alpha)^{-1}\right)\log(kM/\beta)\right\rceil,
--   \quad n=kn_0+m.
--   $$
--   This schedule exists, its blocks and grid are nonempty, and Algorithm 1 is $(\varepsilon,\delta)$-DP on every deterministic replacement-neighboring dataset of size $n$. For every Borel probability law $P$ on $\mathbb R^d\times\{-1,1\}$ with first marginal $N(0,I_d)$, its measurable output classifier satisfies
--   $$
--   \Pr_{S\sim P^n,\,\text{learner coins}}[\operatorname{err}_P(h)\le\mathrm{OPT}+\alpha]\ge1-\beta,
--   \qquad \mathrm{OPT}=\inf_{w,t}\operatorname{err}_P(\operatorname{sign}(\langle w,x\rangle+t)).
--   $$
--   The exact sample upper bound is
--   $$
--   n\le k\left[3+\frac{4C^2D}{c^2\alpha^2}+\frac{4CD\sqrt{\log(1/\delta)}}{c\varepsilon\alpha}\right]
--   +1+C\left(\alpha^{-2}+(\varepsilon\alpha)^{-1}\right)\log(kM/\beta).
--   $$
--   On every input and every random tape, the fixed learner program halts using at most $A(npD+kn_0^2D+kMmD)$ operations, and at most $3An^3$ operations. Its output law is exactly the composition specified by Algorithm 1. At every positive degree (including every scheduled degree), the optimizer itself has a uniform operational realization with cost at most $A(npD+n^2D)$ and expected empirical excess loss at most $2AT\sqrt{D\log(1/\delta)}/(n\varepsilon)$.
--
--   This is the full improper agnostic guarantee with arbitrary conditional binary labels, both error coefficients exactly one, and no realizability, margin, bounded-support or homogeneous-halfspace restriction. The paper writes $\widetilde O(D/\alpha^2+D/(\varepsilon\alpha))$ and $O(npD+kn_0^2D+kMmD)$; its schedule (14a)–(14c), pp.25–26, gives the displayed explicit sample coefficients, and p.27 gives the universal operation constant $A$.
--
--   Differences from the source:
--   - encoding: binary real labels and a classifier on Euclidean R^d → Bool labels decoded as ±1, EuclideanSpace coordinates, a coefficient/threshold output and measurable decoding; reason: retains continuous real inputs, every affine comparison halfspace and arbitrary conditional labels; fixes sign(0)=+1
--   - encoding: sufficiently large universal constants and soft-O sample size → universal C,c,Cdim,A before every instance, the least integer schedule (14) and its explicit upper bound; reason: the proof gives the dimension threshold and numerical rounding coefficients; only the paper’s parameter logarithms are hidden
--   - encoding: Algorithm 1 calls a private ERM algorithm and runs in polynomial arithmetic time → existential sample-only probability optimizer and fixed finite programs with operational realization and charged runtime conclusions; reason: no population law, optimizer correctness or efficiency certificate is supplied as a premise; every sample value is read through the defined input layout
--   - reading: the p.27 arithmetic-operation account does not enumerate a scalar instruction alphabet → the published rational-literal sampling real RAM with integer pointers, sqrt, exp, log and standard Gaussian/exponential draws; reason: norms, projections and exact exponential weights use these scalar real operations; no optimization or feature-evaluation oracle is added, and rational literals constrain programs rather than input examples
--   - encoding: probability over i.i.d. samples and all independent algorithm randomness → product sample measures, independent optimizer laws and normalized finite validation weights; reason: mass-one and measurability conclusions exclude default pushforward or bind values; duplicate candidate indices retain their weights
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 4–6, 25–27, Theorem 2.1, Algorithm 1, Eqs. (14a)–(14c), (16)–(21); canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

/-- Theorem 2.1 and the precise public schedule (14). Neither program nor optimizer can
access P. All optimizer and learning guarantees below are conclusions. -/
theorem theorem_2_1 :
    ∃ (C c Cdim A : ℝ) (O : Optimizer) (optimizerCode learnerCode : LearnerProgram),
      1 ≤ C ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 1 ≤ A ∧ 0 < Cdim ∧
      2 * (C + 1) ^ 2 / c ≤ Cdim ∧
      (∀ (d p n : ℕ), 1 ≤ p → 2 ≤ n → ∀ (ε δ : ℝ),
        0 < ε ∧ ε ≤ 1 / 2 → 0 < δ ∧ δ ≤ 1 / 2 →
        Measurable (fun S => (O d p n ε δ S : Measure (UnitBall d p))) ∧
        PrivateUniformGen.Characterization.IsDP (O d p n ε δ) ε δ ∧
        ∀ S : Fin n → Example d,
          Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val -
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
            (O d p n ε δ S : Measure (UnitBall d p)) ∧
          (∫ v : UnitBall d p, empiricalLoss d p S v.val -
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
            ∂(O d p n ε δ S : Measure (UnitBall d p))) ≤
              A * 2 * radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
                ((n : ℝ) * ε) ∧
          ∃ fuel cost : ℕ,
            (cost : ℝ) ≤ A * ((n : ℝ) * p * featureDimension d p + n ^ 2 * featureDimension d p) ∧
            Implements optimizerCode fuel cost d p 1 (optimizerInput d p n ε δ S)
              ((O d p n ε δ S : Measure (UnitBall d p)).map (fun v => (v, (0 : Fin 1))))) ∧
      ∀ (α β ε δ : ℝ),
        0 < α ∧ α ≤ 1 / 2 → 0 < β ∧ β ≤ 1 / 2 →
        0 < ε ∧ ε ≤ 1 / 2 → 0 < δ ∧ δ ≤ 1 / 2 →
      ∀ (d : ℕ), Cdim / α ^ 5 ≤ (d : ℝ) →
      let p := scheduledDegree C α
      let D := featureDimension d p
      let k := repetitions β
      let M := thresholds C α
      let n₀ := trainingSize C c α ε δ d p
      let m := validationSize C α β ε k M
      let n := k * n₀ + m
      blockCondition C c α ε δ d p n₀ ∧
      (∀ r, blockCondition C c α ε δ d p r → n₀ ≤ r) ∧
      0 < k ∧ 0 < M ∧ 0 < m ∧
      (n : ℝ) ≤ (k : ℝ) * (3 + 4 * C ^ 2 * D / (c ^ 2 * α ^ 2) +
          4 * C * D * Real.sqrt (Real.log (1 / δ)) / (c * ε * α)) + 1 +
        C * (α⁻¹ ^ 2 + (ε * α)⁻¹) * Real.log ((k : ℝ) * M / β) ∧
      ∃ L : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) n,
        (∀ S, (L S : Measure (Output d p M)) = algorithmLaw O d p k M n₀ m ε δ S) ∧
        Measurable (fun S => (L S : Measure (Output d p M))) ∧
        PrivateUniformGen.Characterization.IsDP L ε δ ∧
        (∀ o, Measurable (decode d p M o)) ∧
        (∀ S, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ A * ((n : ℝ) * p * D + (k : ℝ) * n₀ ^ 2 * D + (k : ℝ) * M * m * D) ∧
          (cost : ℝ) ≤ 3 * A * (n : ℝ) ^ 3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (L S : Measure (Output d p M))) ∧
        ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = gaussian d →
          Measurable (fun o => error P (decode d p M o)) ∧
          let ν := (Measure.pi (fun _ : Fin n => P)).bind (fun S => (L S : Measure (Output d p M)))
          IsProbabilityMeasure ν ∧
          ν.real {o | error P (decode d p M o) ≤ opt d P + α} ≥ 1 - β := by sorry

end PrivateAgnosticHalfspace.Gaussian
