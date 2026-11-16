-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_Supplement_theorem_4_2
-- name    : RandomOracleUnitarySynthesis.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:37:32.304198+00:00
-- url     : https://prove2.me/theorems/315a422c-4977-40fa-a4c2-379097509fc6
-- title:
--   Theorem 4.2 (companion theorem; not used in the proof of the goal) — ROM-PRU query bound
-- statement:
--   Fix $\gamma>0$ and $c_T>0$. There is $c>0$ depending only on these two numbers such that the following holds for every family of random-oracle circuits with arbitrary total and oracle-register sizes. Suppose eventually $k_n\ge1$, $0\le\varepsilon_n,\delta_n<1$, the circuit and a standard non-adaptive $T_n$-design law $\nu_n$ admit a channel coupling with diamond error at most $\varepsilon_n$ almost surely, and $T_n\ge c_TN^{1+\gamma}$, where $N=2^n$. If $N^2(1-\varepsilon_n)\to\infty$, then eventually
--
--   $$cN^{\min\{\gamma,1\}}\le k_n^2(1-\delta_n)^{-2}(1-\varepsilon_n)^{-6}.$$
--
--   Moreover, for every $B>0$ and $d\ge0$ bounding both inverse gaps by $B(n+1)^d$ eventually, there exist $B'>0,d'\ge0$ such that eventually
--
--   $$k_n\ge\frac{N^{\min\{\gamma,1\}/2}}{B'(n+1)^{d'}}.$$
--
--   The shared polynomial bound loses no cases: any two polynomial bounds can be enlarged to a common one. This companion theorem is not used in the proof of the retained goal.
--
--   Differences from the source:
--   - generalization: Definition 3.3 uses a deterministic target assignment and adaptive forward-query security → arbitrary channel couplings with almost-sure error and standard non-adaptive design security; reason: Remarks 3.4 and 4.3 explicitly extend the lower bound to this class; every literal ROM-PRU satisfies it
--   - encoding: asymptotic O, Omega, omega and polynomial bounds → positive constants before the families, eventual atTop quantifiers, real powers and the published gap predicates; reason: makes all uniformity and thresholds explicit without changing the asymptotic instances
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Theorem 4.2, printed p. 17 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_rom

open MeasureTheory Filter
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-- Theorem 4.2, printed p.17 / PDF p.19, BOTH conclusions. The lower-bound
constant depends only on gamma and the query-growth constant, never on a family.
Remarks 3.4 and 4.3 permit arbitrary channel couplings and non-adaptive designs. -/
theorem theorem_4_2 :
    ∀ γ : ℝ, 0 < γ → ∀ cT : ℝ, 0 < cT → ∃ c : ℝ, 0 < c ∧
    ∀ (m m₀ k T : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n))
      (δ ε : ℕ → ℝ) (ν : (n : ℕ) → Measure (synthesis_Unitary n))
      (Γ : (n : ℕ) → Measure (synthesis_Channel n × synthesis_Channel n)),
      ROMAdmissible m m₀ k T C δ ε ν Γ → synthesis_GapRegime ε →
      (∀ᶠ n : ℕ in atTop, cT * Real.rpow ((2 : ℝ)^n) (1+γ) ≤ (T n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, c * Real.rpow ((2 : ℝ)^n) (min γ 1) ≤
        (k n : ℝ)^2 * ((1-δ n)⁻¹)^2 * ((1-ε n)⁻¹)^6) ∧
      (∀ B d : ℝ, 0 < B → 0 ≤ d →
        synthesis_PolynomialGap ε B d → synthesis_PolynomialGap δ B d →
        ∃ B' d' : ℝ, 0 < B' ∧ 0 ≤ d' ∧
          ∀ᶠ n : ℕ in atTop,
            Real.rpow ((2 : ℝ)^n) (min γ 1 / 2) /
              (B' * Real.rpow ((n : ℝ)+1) d') ≤ (k n : ℝ)) := by sorry

end RandomOracleUnitarySynthesis.Supplement
