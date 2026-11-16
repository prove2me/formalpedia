-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_Supplement_lemma_4_14
-- name    : RandomOracleUnitarySynthesis.Supplement.lemma_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:36:42.522206+00:00
-- url     : https://prove2.me/theorems/96cd5873-40b7-4b98-bb50-f344ef010dc2
-- title:
--   Lemma 4.14 (used in the proof of Theorem 4.2) — ROM-PRU correlation net
-- statement:
--   Let $N=2^n$ and let a family of random-oracle circuits, target unitary laws $\nu_n$, and channel couplings have almost-sure error $0\le\varepsilon_n<1$, standard design error $0\le\delta_n<1$, and $k_n\ge1$, eventually. Assume $N^2(1-\varepsilon_n)\to\infty$. There is an absolute constant $B>0$, independent of the family and of $\beta$, such that eventually, for every $0<\beta<1$, a nonempty finite set $\mathcal T$ of nonidentity Pauli/Hermitian spectral-contraction pairs satisfies
--
--   $$\log_2|\mathcal T|\le B\left(\frac{Nk_n^2}{\beta^2(1-\varepsilon_n)^4}+n\right),$$
--   $$\Pr_{U\sim\nu_n}\left[\exists(Q,A)\in\mathcal T:\ N^{-1}\operatorname{Re}\operatorname{tr}(AU^\dagger QU)\ge(1-\varepsilon_n)/8\right]\ge1-\beta.$$
--
--   This supplies the correlation net used by Theorem 4.2. The net contains pairs, and the probability is taken under the explicit target law.
--
--   Differences from the source:
--   - generalization: Definition 3.3 uses a deterministic target assignment and adaptive forward-query security → arbitrary channel couplings with almost-sure error and standard non-adaptive design security; reason: Remarks 3.4 and 4.3 explicitly extend the lower bound to this class; every literal ROM-PRU satisfies it
--   - generalization: the conditions of Theorem 4.2 include T = Omega(N^(1+gamma)) → any standard non-adaptive design query count T; reason: the proof of Lemma 4.14 never uses the design-query growth assumption
--   - encoding: asymptotic O, Omega, omega and polynomial bounds → positive constants before the families, eventual atTop quantifiers, real powers and the published gap predicates; reason: makes all uniformity and thresholds explicit without changing the asymptotic instances
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.14, printed p. 31 (PDF p. 33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_rom

open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-- Lemma 4.14, printed pp.31–32 / PDF pp.33–34. The absolute constant is
uniform over beta, all circuit and error families, and the design parameters.
The unused growth assumption on T is dropped (the proof never uses it). -/
theorem lemma_4_14 :
    ∃ B : ℝ, 0 < B ∧ ∀ (m m₀ k T : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n))
      (δ ε : ℕ → ℝ) (ν : (n : ℕ) → Measure (synthesis_Unitary n))
      (Γ : (n : ℕ) → Measure (synthesis_Channel n × synthesis_Channel n)),
      ROMAdmissible m m₀ k T C δ ε ν Γ → synthesis_GapRegime ε →
      ∀ᶠ n : ℕ in atTop, ∀ β : ℝ, 0 < β → β < 1 →
        ∃ net : Finset (synthesis_Pauli n × synthesis_Mat n), net.Nonempty ∧
          (∀ pair ∈ net, pair.1 ≠ (fun _ => 0) ∧ pair.2.IsHermitian ∧
            synthesis_IsContraction pair.2) ∧
          Real.logb 2 (net.card : ℝ) ≤
            B * ((2 : ℝ)^n * (k n : ℝ)^2 / (β^2 * (1-ε n)^4) + (n : ℝ)) ∧
          ENNReal.ofReal (1-β) ≤ (ν n)
            {U | ∃ pair ∈ net, (1-ε n)/8 ≤ synthesis_correlation pair.2 pair.1 U} := by sorry

end RandomOracleUnitarySynthesis.Supplement
