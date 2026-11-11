-- Prove2me | Theorems.Thm_PrivInfoHier_Main_theorem_3_2
-- name    : PrivInfoHier.Main.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:54.044501+00:00
-- url     : https://prove2.me/theorems/24f1d650-45b9-440a-838b-d69f2d7bf1ae
-- title:
--   Theorem 3.2 — utility separation between spec- and mechanism-level privacy filters
-- statement:
--   Let $\mathcal X$ be a database space with a neighbouring relation $\sim$ containing a pair $x\sim x'$ with $x\ne x'$, and let the analyst's requests range over a nonempty measurable space $\mathcal R$. **Theorem 3.2.** Fix $\varepsilon>0$. There is a family of data-release processes $(\mathcal M_i)_{i\ge1}$, parametrised by $\theta\in(0,1)$ (with an output space chosen together with the family), such that for every $\theta\in(0,1)$ and every $\delta\in(0,1)$:
--
--   (a) there exists an $(\varepsilon,\delta)$-valid **mechanism-level** filter — with internal randomness, a finite horizon $N$, every event $\{T\ge t\}\in\sigma(Z,M^t)$, and not spec-level — whose stopping time $T_M$ satisfies
--   $$U_\delta(T_M)\ \ge\ \frac1\theta\cdot\frac{e-1}{e}-\frac\delta\theta-1;$$
--
--   (b) every **spec-level** filter (any internal randomness, $\{T\ge t\}\in\sigma(Z)$) satisfying $(\varepsilon,\delta)$-validity has stopping time $T_S$ with
--   $$U_\delta(T_S)\ \le\ \frac{h(\delta)}{\theta(1-\delta)}+1,$$
--   where $h(\delta)=-\delta\log\delta-(1-\delta)\log(1-\delta)$ is the binary entropy in nats.
--
--   Validity holds for every request strategy, every ordered neighbouring pair and every measurable set of stopped transcripts; $U_\delta$ is the infimum over every database and every request strategy of $\frac1{1-\delta}\int_0^{1-\delta}Q_T$. As $\theta\to0$ the mechanism-level utility grows like $1/\theta$ while the spec-level utility is $O(h(\delta)/\theta)$, which is the separation.
--
--   Differences from the source:
--   - reading: "Let $\mathcal X$ be the space of databases with a neighbouring relation $\sim$" → every database type with a relation that has some $x\sim x'$, $x\ne x'$; reason: without such a pair every filter is valid and (b) fails, so this is the non-degenerate reading of §2.1.
--   - reading: "a set of allowed requests" → every nonempty measurable request type; reason: the theorem is about the model of §2.1, whose request set is arbitrary; with no request there is no strategy.
--   - encoding: the output space of the processes → chosen existentially with the family (with its σ-algebra); reason: the process family is existential, and its unsafe mechanism outputs the database.
--   - generalization: "$T\le N$ almost surely" for the filter of (a) → $T(\omega)\le N$ for every $\omega$; reason: pointwise implies almost surely, so (a) as stated implies (a) as printed.
--   - generalization: (b) over spec-level filters with a finite horizon → over all spec-level filters with ℕ-valued stopping times, no horizon; reason: filters with a horizon are a special case.
--   - encoding: the common probability space → $\Omega=\mathcal Z\times(\mathcal R\times\mathcal Y)^{\mathbb N}$ with $\mathrm{law}(Z)\otimes P_{x,\mathcal A}$, $P_{x,\mathcal A}$ built by Ionescu-Tulcea, mechanisms carrying the discrete σ-algebra, stopped transcripts in a sigma type; reason: this is the canonical realisation of the paper's model; the information σ-algebras do not depend on $x$ or $\mathcal A$, as p. 7 requires.
--   - reading: "the quantile function" → $Q(u)=\inf\{t\in\mathbb N:P(T\le t)\ge u\}$; reason: the paper does not fix a convention; other conventions differ on a countable set and give the same $U_\delta$.
--   - encoding: $U_\delta$ real → $U_\delta\in[0,\infty]$ (lower Lebesgue integral, infimum in $[0,\infty]$), bounds through `ENNReal.ofReal`; reason: $U_\delta\ge0$, so "$U_\delta\ge$ a negative number" is trivially true in both readings.
--   - encoding: $\theta\in(0,1)$ → `θ : Set.Ioo 0 1`; $h$ → `Real.binEntropy`; reason: same values.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 9 (PDF 11), Theorem 3.2; proof App. B.1, pp. 17–19 (PDF 19–21)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- Theorem 3.2 (utility separation between spec- and mechanism-level filtering). For every
database space with a neighbouring pair `x ∼ x′`, `x ≠ x′`, every nonempty request space and every
`ε > 0` there is a family of data-release processes indexed by `θ ∈ (0, 1)` such that for every
`θ` and every `δ ∈ (0, 1)`: (a) some `(ε, δ)`-valid mechanism-level filter of finite horizon has
`U_δ(T_M) ≥ (1/θ)(e − 1)/e − δ/θ − 1`; (b) every `(ε, δ)`-valid spec-level filter has
`U_δ(T_S) ≤ h(δ)/(θ(1 − δ)) + 1`, `h` the binary entropy in nats. -/
theorem theorem_3_2 (𝒳 : Type) (nb : 𝒳 → 𝒳 → Prop) (hnd : ∃ x x' : 𝒳, nb x x' ∧ x ≠ x')
    (ℛ : Type) [MeasurableSpace ℛ] [Nonempty ℛ] (ε : ℝ) (hε : 0 < ε) :
    ∃ (𝒴 : Type) (_ : MeasurableSpace 𝒴) (proc : Set.Ioo (0 : ℝ) 1 → Process 𝒳 ℛ 𝒴),
      ∀ (θ : Set.Ioo (0 : ℝ) 1) (δ : ℝ), 0 < δ → δ < 1 →
        (∃ (𝒵 : Type) (_ : MeasurableSpace 𝒵) (μZ : Measure 𝒵) (_ : IsProbabilityMeasure μZ)
            (T : 𝒵 × Path ℛ 𝒴 → ℕ) (N : ℕ),
            Measurable T ∧ (∀ ω, T ω ≤ N) ∧ IsValid (proc θ) nb ε δ μZ T ∧
            IsMechanismLevel (proc θ) T ∧
            ENNReal.ofReal ((1 / θ.1) * ((Real.exp 1 - 1) / Real.exp 1) - δ / θ.1 - 1)
              ≤ filterClippedMean (proc θ) μZ T δ) ∧
        (∀ (𝒵 : Type) [MeasurableSpace 𝒵] (μZ : Measure 𝒵) [IsProbabilityMeasure μZ]
            (T : 𝒵 × Path ℛ 𝒴 → ℕ),
            IsSpecLevel T → IsValid (proc θ) nb ε δ μZ T →
            filterClippedMean (proc θ) μZ T δ
              ≤ ENNReal.ofReal (Real.binEntropy δ / (θ.1 * (1 - δ)) + 1)) := by sorry

end PrivInfoHier.Main
