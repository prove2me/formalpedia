-- Prove2me | Theorems.Thm_StochAutoreg_proposition_4_2
-- name    : StochAutoreg.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:34.679265+00:00
-- url     : https://prove2.me/theorems/2b5d3a55-c52d-49a9-a0c2-7a6eef4bfe2a
-- title:
--   Proposition 4.2 — finite generator classes: expected error, full-trajectory law, and $m\le\lceil 3\log(|\mathcal F|+1)/\varepsilon\rceil$
-- statement:
--   Let $\mathcal F$ be a finite generator class and $M\ge1$. For every $n\ge1$ and each supervision $b\in\{\mathrm{CoT},\mathrm{e2e}\}$, a learner using $n$ samples outputs $\hat q$ such that, for every $g_\star\in\mathcal F$ and prompt law $P$,
--
--   $$\mathbb E\bigl[\mathbb E_{X\sim P}\mathrm{KL}(q_\star(X)\|\hat q(X))\bigr]\le\frac{\log(|\mathcal F|+1)}n.$$
--
--   Given $n$ i.i.d. CoT samples, a learner also outputs a full-trajectory conditional law $\widehat Q^M$ with the same bound for $\mathbb E[\mathbb E_{X\sim P}\mathrm{KL}(P^M_{g_\star}(\cdot\mid X)\|\widehat Q^M(\cdot\mid X))]$. In particular, for every $\varepsilon>0$ and each $b$,
--
--   $$m^{\mathcal F,M}_b(\varepsilon)\le\Bigl\lceil\frac{3\log(|\mathcal F|+1)}\varepsilon\Bigr\rceil.$$
--
--   This makes all sample complexities of a finite class finite.
--
--   Differences from the source:
--   - encoding: |F| and the KL between laws on {0,1}^M → F.ncard with F finite, and Mathlib's klDiv of the laws, in ℝ≥0∞; reason: Lean representation of the same quantities
--   - encoding: m_b(ε), with δ omitted → m_b(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: "random seeds" → one seed uniform on [0,1]; reason: the paper names no seed space, and a uniform point of [0,1] simulates any standard Borel seed
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Proposition 4.2, p.10

import Mathlib
import Definitions.Def_StochAutoreg_risk
import Definitions.Def_StochAutoreg_Learner
import Definitions.Def_StochAutoreg_iidSeedMeasure
import Definitions.Def_StochAutoreg_cotLaw
import Definitions.Def_StochAutoreg_e2eLaw
import Definitions.Def_StochAutoreg_qE2E
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E
import Definitions.Def_StochAutoreg_promptMeasurableSpace
open MeasureTheory

namespace StochAutoreg

/-- **Proposition 4.2** (finite classes). For every finite generator class `F`, and `M, n ≥ 1`, a learner using `n` samples
with supervision `b ∈ {CoT, e2e}` has expected error at most `log(|F|+1)/n`, for every `g⋆ ∈ F` and prompt law `P`; given `n`
CoT samples a learner also outputs a full-trajectory conditional law `Q̂^M` with the same bound for
`E[E_{X∼P} KL(P^M_{g⋆}(·|X)‖Q̂^M(·|X))]`; and `m^{F,M}_b(ε) ≤ ⌈3 log(|F|+1)/ε⌉` for every `ε > 0`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Proposition 4.2, p.10.

**Formalization Note.** `|F|` is `F.ncard`, and `m_b(ε)` is at confidence `δ = 1/3` as on p.3. The KL between finite laws is
Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`. -/
theorem proposition_4_2 (F : Set Generator) (hF : F.Finite) (M : ℕ) (hM : 1 ≤ M) :
    (∀ n : ℕ, 1 ≤ n →
      (∃ A : Learner (List Bool × (Fin M → Bool)) n, ∀ g ∈ F, ∀ P : PMF (List Bool),
        ∫⁻ w, risk P (qE2E g M) (A.run w.1 w.2) ∂iidSeedMeasure (cotLaw g M P) n ≤
          ENNReal.ofReal (Real.log ((F.ncard : ℝ) + 1) / (n : ℝ))) ∧
      (∃ A : Learner (List Bool × Bool) n, ∀ g ∈ F, ∀ P : PMF (List Bool),
        ∫⁻ w, risk P (qE2E g M) (A.run w.1 w.2) ∂iidSeedMeasure (e2eLaw g M P) n ≤
          ENNReal.ofReal (Real.log ((F.ncard : ℝ) + 1) / (n : ℝ))) ∧
      (∃ Qhat : (Fin n → List Bool × (Fin M → Bool)) → unitInterval → List Bool →
          PMF (Fin M → Bool),
        (∀ s x z, Measurable fun u => Qhat s u x z) ∧
        ∀ g ∈ F, ∀ P : PMF (List Bool),
          ∫⁻ w, ∑' x, P x * InformationTheory.klDiv (trajPMF g M x).toMeasure
              (Qhat w.1 w.2 x).toMeasure ∂iidSeedMeasure (cotLaw g M P) n ≤
            ENNReal.ofReal (Real.log ((F.ncard : ℝ) + 1) / (n : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε →
      mCoT F M ε (1 / 3) ≤ ((⌈3 * Real.log ((F.ncard : ℝ) + 1) / ε⌉₊ : ℕ) : ℕ∞) ∧
      mE2E F M ε (1 / 3) ≤ ((⌈3 * Real.log ((F.ncard : ℝ) + 1) / ε⌉₊ : ℕ) : ℕ∞)) := by sorry

end StochAutoreg
