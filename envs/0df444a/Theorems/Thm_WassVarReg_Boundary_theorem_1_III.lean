-- Prove2me | Theorems.Thm_WassVarReg_Boundary_theorem_1_III
-- name    : WassVarReg.Boundary.theorem_1_III
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:02.740984+00:00
-- url     : https://prove2.me/theorems/08ea25a3-1c12-40a5-adee-29ef919bb4be
-- title:
--   Theorem 1(III), first display, p. 8 — w.p. ≥ 1 − e^{−t}, E_{P_n}[(ρ − d(z, D_f))₊] ≤ Cρ² + 2ρE_⊗[ℜ_n(I_ρ)] + ρ√(t/2n) for every f
-- statement:
--   Let $(\mathcal Z, d)$ be a second-countable metric space with its Borel $\sigma$-algebra and $P_{\rm true}$ a probability measure on it. Let $\mathcal F$ be a set of losses and, for each $f \in \mathcal F$, let $\mathcal D_f \subseteq \mathcal Z$ be its closed, $P_{\rm true}$-null set of non-smooth points (Assumption 1). Write $d(z, D) = \inf_{\tilde z \in D} d(z, \tilde z)$ with $d(z, \varnothing) = +\infty$, let
--   $$\mathcal I_\rho = \bigl\{z \mapsto \mathbf 1\{d(z, \mathcal D_f) < \rho\} : f \in \mathcal F,\ \mathcal D_f \ne \varnothing\bigr\},$$
--   and let $P_n$ be the empirical law of an i.i.d. sample of size $n \ge 1$ from $P_{\rm true}$. Assume Assumption 3 (bounded density) holds. Then there exist $\bar\rho > 0$ and $C > 0$ such that for all $n \ge 1$, all $t > 0$ and all $0 \le \rho < \bar\rho$, with probability at least $1 - e^{-t}$, for every $f \in \mathcal F$,
--   $$\mathbb E_{P_n}\bigl[(\rho - d(z, \mathcal D_f))_+\bigr] \le C\rho^2 + 2\rho\,\mathbb E_\otimes[\mathfrak R_n(\mathcal I_\rho)] + \rho\sqrt{\frac{t}{2n}}.$$
--
--   The left side is the boundary term in the paper's expansion of the $p$-Wasserstein regularizer for non-smooth losses (Theorem 1(I)–(II)). The theorem shows that it is of second order in $\rho$, up to the Rademacher complexity of $\mathcal I_\rho$ and a $\rho/\sqrt n$ fluctuation, uniformly over the loss class; with $\rho_n = O(1/\sqrt n)$ it is $O_p(1/n)$ for many classes.
--
--   **Formalization Note**
--   1. This is the first display of Theorem 1(III). The second display (Dudley's entropy integral with respect to the empirical $L_2(P_n)$ norm) is not stated: its proof bounds the empirical Rademacher complexity at the observed sample, while Lemma EC.5 needs its expectation, so it does not follow from the argument given.
--   2. $\bar\rho$ and $C$ are chosen before $n$ and $t$ (the page fixes $t$ first); the proof takes them from Assumption 3 alone, so this is the stronger reading.
--   3. The radius satisfies $\rho \ge 0$; the probability is the product measure of the set of samples on which some $f \in \mathcal F$ violates the bound (outer measure; the quantifier over $\mathcal F$ is inside the event).
--   4. Standing and technical hypotheses: each $\mathcal D_f$ is closed and $P_{\rm true}$-null (Assumption 1, p. 6); the space is second countable; and each class $\mathcal I_\rho$ is Rademacher-measurable at every sample size (measurability of the uniform deviation, the empirical Rademacher complexity and the double-sample deviation; true for countable $\mathcal F$). The latter two are technical hypotheses left implicit by the paper.
--   5. The distance is the extended distance, so a loss with $\mathcal D_f = \varnothing$ has boundary term $0$.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Theorem 1(III), first display, p. 8

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- Theorem 1(III), first display, p. 8. `hD`: each `D_f` is closed and `P_true`-null
(Assumption 1, p. 6); `hguard`: measurability guard for the classes `I_ρ`. -/
theorem theorem_1_III {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    (Ptrue : ProbabilityMeasure Z) (F : Set (Z → ℝ)) (D : (Z → ℝ) → Set Z)
    (hD : ∀ f ∈ F, IsClosed (D f) ∧ (Ptrue : Measure Z) (D f) = 0)
    (hguard : ∀ (n : ℕ) (ρ : ℝ), RademacherMeasurable n Ptrue (indicatorClass ρ F D))
    (hA3 : Assumption3 Ptrue F D) :
    ∃ ρbar > 0, ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 ≤ ρ → ρ < ρbar →
      MinimaxWass.DataDep.sampleLaw n Ptrue
        {ω | ¬ ∀ f ∈ F, (1 / (n : ℝ)) * ∑ i : Fin n, WassVarReg.PInf.boundaryGap ρ (D f) (ω i) ≤
          C * ρ ^ 2 + 2 * ρ * rademacher n Ptrue (indicatorClass ρ F D) +
            ρ * Real.sqrt (t / (2 * n))} ≤
        ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassVarReg.Boundary
