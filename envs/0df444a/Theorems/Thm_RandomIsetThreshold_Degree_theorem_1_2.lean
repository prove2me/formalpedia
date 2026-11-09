-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_theorem_1_2
-- name    : RandomIsetThreshold.Degree.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:10:56.880713+00:00
-- url     : https://prove2.me/theorems/f969ecdc-4011-451a-982d-a9b4fcc97d26
-- title:
--   Theorem 1.2 — full hypergraph degree threshold
-- statement:
--   Fix an integer $r\ge2$ and $0<\varepsilon<r^{1/(r-1)}-1$. There are $d,\gamma_0>0$ depending only on $r,\varepsilon$. For each $0<\delta<1/2$, choose $\xi>0$ and an integer $n_0>0$ depending only on $r,\varepsilon,\delta$. For each $\lambda\ge3$, choose $c>0$ depending only on $r,\varepsilon,\delta,\lambda$. For every $0<\gamma\le\gamma_0$, put $C=56/(\gamma\delta)$. Uniformly for $n\ge n_0$, $d/n^{r-1}\le p\le1-n^{-\xi}$ and real $D>0$:
--
--   1. Every seedwise measurable random polynomial $f$ of degree at most $D\le cpL^r$, with arbitrary independent probability seed and $\mathbb E\|f(H_{n,p},R)\|_2^2\le\lambda L$, satisfies
--
--   $$\Pr\bigl(\exists I\text{ independent}:\ |I|\ge(1+\varepsilon)L,\ \|f(H_{n,p},R)-1_I\|_2^2\le\gamma|I|\bigr)\le\delta.$$
--
--   2. If $D\ge CpL^r$, there is a deterministic polynomial $f$ with degree at most $CpL^r\le D$ and
--
--   $$\mathbb E\|f(H_{n,p})\|_2^2\le\lceil(1+\varepsilon)L\rceil\le3L\le\lambda L,$$
--
--   whose success probability for the same event is at least $1-\delta$.
--
--   This states both branches of the degree threshold, including the deterministic witness and its sharper norm bound. It imposes no bound on evaluation time. **Formalization Note** The paper writes $O(\delta)$ and $1-O(\delta)$; Theorem 1.5 and Remark 1.6 give the explicit upper bound $\delta$, while §2.3 equation (24) gives $1-\delta$ with exactly $C=56/(\gamma\delta)$.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - encoding: supremum success probability over admissible random polynomials → a universal upper bound and a deterministic admissible lower witness; reason: these give both supremum branches without taking a real supremum over a universe of seed spaces
--   - generalization: O(δ) and 1-O(δ), with a ceiling norm bound for the witness → success at most δ or at least 1-δ, C = 56/(γδ), and ceiling ≤ 3L ≤ λL; reason: Theorem 1.5 and Remark 1.6 on p. 4 give the first bound; equations (21)–(24) on p. 9 give the witness, its admissibility, and the second bound
--   - encoding: integer ceiling of (1+ε)L → Nat ceiling cast to ℝ; reason: the source regime makes (1+ε)L positive, so this is the same integer ceiling
--   - encoding: the closing sentence naming the deterministic witness without reference to D → the witness stated under the branch hypothesis CpL^r ≤ D; reason: D := CpL^r is itself positive and allowed (pL^r ≥ 1), so the unconditional sentence is recovered
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 3, Theorem 1.2, equation (3); explicit bounds p. 4, Theorem 1.5 and Remark 1.6, and p. 9, equations (21)–(24)

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput

open MeasureTheory
open scoped ENNReal BigOperators
universe u_theorem_1_2

namespace RandomIsetThreshold.Degree

theorem theorem_1_2
(r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε ∧ ε < rootFactor r - 1) :
    ∃ d γ₀ : ℝ, 0 < d ∧ 0 < γ₀ ∧
      ∀ δ : ℝ, 0 < δ ∧ δ < 1 / 2 →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ lam : ℝ, 3 ≤ lam → ∃ c : ℝ, 0 < c ∧
      ∀ γ : ℝ, 0 < γ ∧ γ ≤ γ₀ →
      let C := 56 / (γ * δ)
      ∀ n : ℕ, n₀ ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
      ∀ D : ℝ, 0 < D →
      let L := scale n r p
      (D ≤ c * (p : ℝ) * L ^ r →
        ∀ (Ω : Type u_theorem_1_2) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (f : Cube n r → Ω → Vector n), SeedMeasurable f → RandomDegreeLE μ f D →
          normMoment p μ f ≤ ENNReal.ofReal (lam * L) → successProbability p μ f ε γ ≤ δ) ∧
      (C * (p : ℝ) * L ^ r ≤ D →
        ∃ f : Cube n r → Vector n,
          DegreeLE f (C * (p : ℝ) * L ^ r) ∧ C * (p : ℝ) * L ^ r ≤ D ∧
          detNormMoment p f ≤ ENNReal.ofReal (⌈(1 + ε) * L⌉₊ : ℝ) ∧
          (⌈(1 + ε) * L⌉₊ : ℝ) ≤ 3 * L ∧ 3 * L ≤ lam * L ∧
          1 - δ ≤ detSuccessProbability p f ε γ) := by sorry

end RandomIsetThreshold.Degree
