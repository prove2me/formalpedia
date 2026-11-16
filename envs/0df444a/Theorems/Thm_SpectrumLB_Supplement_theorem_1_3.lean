-- Prove2me | Theorems.Thm_SpectrumLB_Supplement_theorem_1_3
-- name    : SpectrumLB.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:59:40.810487+00:00
-- url     : https://prove2.me/theorems/5775f08c-b819-41db-8352-6ef831949c68
-- title:
--   Theorem 1.3 — estimating the von Neumann entropy to constant precision needs $\Omega(d^{2-2/(k/2+2)})$ copies
-- statement:
--   Let $S(\rho)=-\mathrm{Tr}(\rho\ln\rho)$ be the von Neumann entropy of a $d$-dimensional state. For every even integer $k\ge 2$ there exist a precision $\epsilon_k>0$, a constant $c>0$ and a dimension $d_0$, none depending on $d$, such that the following holds for every $d\ge d_0$ and every $n$: if a measurement of $n$ copies of an unknown $d$-dimensional state $\rho$ outputs a real number $\widehat S$ with
--
--   $$
--   \Pr\big[\,|\widehat S-S(\rho)|\le\epsilon_k\,\big]\ \ge\ \frac23\qquad\text{for every density matrix }\rho,
--   $$
--
--   then
--
--   $$
--   n\ \ge\ c\, d^{\,2-\frac{2}{k/2+2}} .
--   $$
--
--   Letting $k$ grow, $d^{2-o(1)}$ copies are needed to estimate the entropy to constant additive error, against the previous $\Omega(d/\log d)$ coming from classical Shannon-entropy estimation; this shows the Empirical Young Diagram algorithm is near-optimal for entropy estimation.
--
--   **Formalization Note** The measurement is any POVM on $n$ copies with real outcomes (`EntropyEstimates`). $\Omega(\cdot)$ is read as $\exists c>0\,\exists d_0\,\forall d\ge d_0$ with $\epsilon_k$ chosen first, exactly as in the mission's goal `SpectrumLB.theorem_1_2`.
--
--   Differences from the source:
--   - encoding: Ω(d^{2−2/(k/2+2)}) copies for a dimension-independent ε_k → ∃ ε > 0, ∃ c > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n, ∀ E, EntropyEstimates d n ε E → c·d^(2 − 2/(k/2+2)) ≤ n (real power); reason: standard reading of Ω with ε independent of d, the same as the published goal SpectrumLB.theorem_1_2
--   - encoding: an algorithm estimating the entropy to within ε (with probability 2/3, as in Definition 1.1) → a POVM on (ℂ^d)^{⊗n} indexed by Fin n → Fin d with real outcomes, success probability ≥ 2/3 on every density matrix; reason: every algorithm on n copies is such a POVM and conversely; the 2/3 convention is Definition 1.1's, used by the proof on p.22
--   - encoding: S(ρ) = −Tr(ρ ln ρ) → MomentPolytopes.QuantumFunctionals.vnEntropy ρ (Shannon entropy of the spectrum, natural log, 0 ln 0 = 0); reason: equal on density matrices, the only arguments
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 1.3, p. 3 (proof sketch p. 23)

import Mathlib
import Definitions.Def_SpectrumLB_Supplement_EntropyEstimates

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **Theorem 1.3 (entropy estimation lower bound).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
Theorem 1.3, p. 3: "For every even k ≥ 2, there exists a dimension-independent ϵk > 0 such that the
copy complexity of estimating a d-dimensional state's von Neumann entropy to within precision ϵk is
at least Ω(d^{2−2/(k/2+2)})."

For every even `k ≥ 2` there are `ε > 0`, `c > 0` and `d₀` such that for all `d ≥ d₀`, all `n` and
every POVM `E` on `(ℂ^d)^{⊗n}` with real outcomes that estimates `S(ρ) = −Tr(ρ ln ρ)` within `ε` with
probability `≥ 2/3` for every state `ρ`, `n ≥ c · d^{2 − 2/(k/2+2)}`.

**Formalization Note.** `Ω(·)` is `∃ c > 0, ∃ d₀, ∀ d ≥ d₀` with `ε` chosen first
("dimension-independent"), as in the published goal `SpectrumLB.theorem_1_2`. Every `d ≥ d₀` is
covered, not only multiples of the hard instance's parameters. The exponent is a real power. -/
theorem theorem_1_3 :
    ∀ k : ℕ, Even k → 2 ≤ k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ,
        ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
          EntropyEstimates d n ε E →
            c * (d : ℝ) ^ ((2 : ℝ) - 2 / ((k : ℝ) / 2 + 2)) ≤ n := by sorry

end SpectrumLB.Supplement
