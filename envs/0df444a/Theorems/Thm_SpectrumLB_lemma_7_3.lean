-- Prove2me | Theorems.Thm_SpectrumLB_lemma_7_3
-- name    : SpectrumLB.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:23.079633+00:00
-- url     : https://prove2.me/theorems/31e8a6d6-7d0d-4841-a6a7-99944f9e208a
-- title:
--   Lemma 7.3 — normalized power sums of $\mathrm{spec}(\rho_e)$ concentrate around $\Psi_j(e)$
-- statement:
--   Let $e=(e_1,\dots,e_K)$ be positive integers and fix an integer $\ell\ge1$. There is a constant $B>0$ such that for every $\varepsilon>0$ the event
--
--   $$
--   \widetilde{\mathcal E}_e(\varepsilon,\ell)=\Big\{\|\rho_e\|_\infty>\frac Bd\ \ \text{or}\ \ \max_{1\le j\le\ell}\big|\mathrm{pow}_j(\mathrm{spec}\,\rho_e)-\Psi_j(e)\big|>\varepsilon\Big\}
--   $$
--
--   for the random state $\rho_e$ of the $n$-tilted ensemble satisfies:
--
--   1. there are $C,c>0$ and $d_0$ such that $\Pr(\widetilde{\mathcal E}_e(\varepsilon,\ell))\le\exp(Cn-c\,d^2)$ for every $d\ge d_0$ divisible by each $e_i$ and every $n$;
--   2. in particular, if $n=o(d^2)$: there are $\eta,c'>0$ and $d_0'$ such that $\Pr(\widetilde{\mathcal E}_e(\varepsilon,\ell))\le\exp(-c'd^2)$ for every such $d\ge d_0'$ and every $n\le\eta d^2$.
--
--   With high probability the spectrum of a state drawn from the ensemble is flat at scale $1/d$ and its normalized power sums are close to their deterministic values $\Psi_j(e)$.
--
--   Differences from the source:
--   - generalization: e ∈ {a, b} → every sequence e of positive integers, B depending on e; reason: the proof uses only ν_e and Lemma 7.2 (paper.md R5); for the pair a, b take the larger B, which only shrinks the event
--   - encoding: (7.20), Pr(Ẽ_a ∪ Ẽ_b) ≤ exp(−Ω(d²)) → the bound for each e separately; reason: the union bound gives the union for any joint law, and the union version implies each part
--   - encoding: n = o(d²) ⇒ exp(−Ω(d²)) → ∃ η > 0, c' > 0, d₀: ∀ d ≥ d₀, ∀ n ≤ η d²; reason: uniform form (paper.md R4)
--   - encoding: exp(O(n) − Ω(d²)) → exp(C n − c d²) for d ≥ d₀ with C, c depending on ε, ℓ, e; reason: meaning of the implicit constants
--   - encoding: ‖ρ_e‖_∞ > B/d → some eigenvalue of ρ_e exceeds B/d; reason: ρ_e is positive semidefinite
--   - encoding: d a multiple of each e_i → 0 < d and e_i ∣ d for all i; reason: Definition 3.4's standing hypothesis
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 7.3, Eqs. (7.18)–(7.20), p. 36

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_spec
import Definitions.Def_SpectrumLB_tiltedHaar
import Definitions.Def_SpectrumLB_prpState
import Definitions.Def_SpectrumLB_powSum
import Definitions.Def_SpectrumLB_psi

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 7.3 (concentration of normalized power sums).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 7.3, Eqs. (7.18)–(7.20), p. 36: "Fix a positive integer ℓ. There is a constant B > 0 such that,
for every ε > 0 and e ∈ {a, b}, the event Ẽ_e(ε, ℓ) := {‖ρ_e‖_∞ > B/d or max_{1≤j≤ℓ} |pow_j(spec(ρ_e)) −
Ψ_j(e)| > ε} satisfies Pr(Ẽ_e(ε, ℓ)) ≤ exp(O(n) − Ω(d^2)). The implicit constants may depend on ε and ℓ. In
particular, if n = o(d^2), then Pr(Ẽ_a(ε, ℓ) ∪ Ẽ_b(ε, ℓ)) ≤ exp(−Ω(d^2))."

**Formalization Note.** Stated for each positive sequence `e` (reading R5), `d ≥ 1`, `e_i ∣ d`; the event is
under the tilted law (`ρ_e = prpState e U`, `U ∼ tiltedHaar d n e`). `‖ρ‖_∞ > B/d` is "some eigenvalue
exceeds `B/d`" (ρ is PSD). (7.19) is `≤ exp(C n − c d^2)` for `d ≥ d₀`; (7.20) is encoded as in reading R4,
for each `e` separately: the union over `e ∈ {a, b}` follows by a union bound and implies each part. -/
theorem lemma_7_3 {K : ℕ} (e : Fin K → ℕ) (he : ∀ i, 0 < e i) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ε : ℝ, 0 < ε →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d → (∀ i, e i ∣ d) →
        ∀ n : ℕ,
          tiltedHaar d n e {U | (∃ i, B / d < OptimalSpectrum.Entangled.spec (prpState e U) i) ∨
              ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧
                ε < |powSum j (OptimalSpectrum.Entangled.spec (prpState e U)) - psi d e j|} ≤
            ENNReal.ofReal (Real.exp (C * n - c * (d : ℝ) ^ 2))) ∧
      (∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d → (∀ i, e i ∣ d) →
        ∀ n : ℕ, (n : ℝ) ≤ η * (d : ℝ) ^ 2 →
          tiltedHaar d n e {U | (∃ i, B / d < OptimalSpectrum.Entangled.spec (prpState e U) i) ∨
              ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧
                ε < |powSum j (OptimalSpectrum.Entangled.spec (prpState e U)) - psi d e j|} ≤
            ENNReal.ofReal (Real.exp (-(c * (d : ℝ) ^ 2)))) := by sorry

end SpectrumLB
