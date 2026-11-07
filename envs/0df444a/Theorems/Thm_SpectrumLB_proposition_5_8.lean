-- Prove2me | Theorems.Thm_SpectrumLB_proposition_5_8
-- name    : SpectrumLB.proposition_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:53.229288+00:00
-- url     : https://prove2.me/theorems/3e6ce0de-5a26-4cf7-ae7d-4ce1a46b3a5a
-- title:
--   Proposition 5.8 — typical spectra of $\rho_a,\rho_b$ are $\delta^{\mathrm{spec}}_k$-separated in sorted TV
-- statement:
--   Let $k\ge1$ and let $a,b$ be sequences of $K$ positive integers with $\sum_ia_i^j=\sum_ib_i^j$ for $1\le j<k$ and $\sum_ia_i^k\ne\sum_ib_i^k$. There are $\delta^{\mathrm{spec}}_k>0$, $\eta>0$, $c>0$ and $d_0$ such that for every $d\ge d_0$ divisible by each $a_i,b_i$ there are Borel sets $\mathcal T^{(d)}_a,\mathcal T^{(d)}_b\subseteq\mathbb R^d$ of spectra with
--
--   $$
--   d^{\downarrow}_{\mathrm{TV}}(\alpha,\beta)\ \ge\ \delta^{\mathrm{spec}}_k\qquad\text{for all }\alpha\in\mathcal T^{(d)}_a,\ \beta\in\mathcal T^{(d)}_b,
--   $$
--
--   and, for every $n\le\eta d^2$ (the regime $n=o(d^2)$) and each $e\in\{a,b\}$,
--
--   $$
--   \Pr\big(\mathrm{spec}(\rho_e)\in\mathcal T^{(d)}_e\big)\ \ge\ 1-e^{-c d^2};
--   $$
--
--   in particular, for any joint law of $(\rho_a,\rho_b)$, $\Pr\big(d^{\downarrow}_{\mathrm{TV}}(\mathrm{spec}\,\rho_a,\mathrm{spec}\,\rho_b)\ge\delta^{\mathrm{spec}}_k\big)\ge1-e^{-cd^2}$. Together with Theorem 5.7 this yields Theorem 1.2: a good spectrum estimator would distinguish the two indistinguishable ensembles.
--
--   Differences from the source:
--   - generalization: a, b from Proposition 5.2 → any K and positive a, b with equal power sums for 1 ≤ j < k and different at k; reason: the proof uses only these properties via Lemmas 7.1 and 7.3 (paper.md R5); Proposition 5.2's sequences satisfy them
--   - generalization: k even, k ≥ 2 (§5 standing assumption, p. 20) → any k ≥ 1; reason: the proof (§7, which fixes an arbitrary k ∈ ℕ, p. 34) uses only Lemmas 7.1 and 7.3, neither of which needs k even; every even k ≥ 2 is an instance
--   - encoding: "Assume that n = o(d²)" → ∃ η > 0 before d, statement for every n ≤ η d²; reason: uniform form (paper.md R4)
--   - encoding: Pr(spec ρ_e ∈ 𝒯_e) ≥ 1 − exp(−Ω_k(d²)) → Pr(spec ρ_e ∉ 𝒯_e) ≤ exp(−c d²), sets 𝒯 Borel and depending on d only; reason: the tilted law is a probability measure, so the two forms agree; the paper's sets (7.32) are closed and depend only on d
--   - generalization: (5.13) for the pair (ρ_a, ρ_b) with unspecified joint law → for every coupling of the two tilted laws; reason: (5.13) follows from (5.11)–(5.12) by a union bound for any joint law; the independent one is a case
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 5.8, Eqs. (5.11)–(5.13), p. 22

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_spec
import Definitions.Def_SpectrumLB_tiltedHaar
import Definitions.Def_SpectrumLB_prpState
import Definitions.Def_SpectrumLB_sortedTV

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Proposition 5.8 (spectral separation).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 5.8, Eqs. (5.11)–(5.13), p. 22: "Assume that n = o(d^2). There exist sets 𝒯_a^{(d)} and
𝒯_b^{(d)} of spectra and a constant δ_k^{spec} > 0 such that, for every e ∈ {a, b},
Pr(spec(ρ_e) ∈ 𝒯_e^{(d)}) ≥ 1 − exp(−Ω_k(d^2)), and d↓TV(α, β) ≥ δ_k^{spec} for every α ∈ 𝒯_a^{(d)} and
β ∈ 𝒯_b^{(d)}. In particular, Pr(d↓TV(spec(ρ_a), spec(ρ_b)) ≥ δ_k^{spec}) ≥ 1 − exp(−Ω_k(d^2))."

**Formalization Note.** `a, b` positive, power sums equal for `1 ≤ j < k` and different at `k` (reading R5),
`k ≥ 1`. "Assume n = o(d^2)" is `n ≤ η d^2` with `η` chosen before `d` (reading R4). The sets depend on `d`
only and are Borel. (5.11) is written as an upper bound on the failure event `spec ∉ 𝒯_e` (equivalent, the
tilted law being a probability measure). (5.13) is stated for every joint law (coupling) of the two random
states, in particular the independent one. -/
theorem proposition_5_8 (k : ℕ) (hk : 1 ≤ k) {K : ℕ} (a b : Fin K → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hpow : ∀ j : ℕ, 1 ≤ j → j < k → ∑ i, a i ^ j = ∑ i, b i ^ j)
    (hsep : ∑ i, a i ^ k ≠ ∑ i, b i ^ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ, 0 < η ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
      (∀ i, a i ∣ d) → (∀ i, b i ∣ d) →
      ∃ Ta Tb : Set (Fin d → ℝ), MeasurableSet Ta ∧ MeasurableSet Tb ∧
        (∀ α ∈ Ta, ∀ β ∈ Tb, δ ≤ sortedTV α β) ∧
        ∀ n : ℕ, (n : ℝ) ≤ η * (d : ℝ) ^ 2 →
          tiltedHaar d n a {U | OptimalSpectrum.Entangled.spec (prpState a U) ∉ Ta} ≤
            ENNReal.ofReal (Real.exp (-(c * (d : ℝ) ^ 2))) ∧
          tiltedHaar d n b {U | OptimalSpectrum.Entangled.spec (prpState b U) ∉ Tb} ≤
            ENNReal.ofReal (Real.exp (-(c * (d : ℝ) ^ 2))) ∧
          ∀ μ : Measure ((Fin K → Matrix.unitaryGroup (Fin d) ℂ) ×
              (Fin K → Matrix.unitaryGroup (Fin d) ℂ)),
            μ.map Prod.fst = tiltedHaar d n a → μ.map Prod.snd = tiltedHaar d n b →
            μ {p | sortedTV (OptimalSpectrum.Entangled.spec (prpState a p.1))
                (OptimalSpectrum.Entangled.spec (prpState b p.2)) < δ} ≤
              ENNReal.ofReal (Real.exp (-(c * (d : ℝ) ^ 2))) := by sorry

end SpectrumLB
