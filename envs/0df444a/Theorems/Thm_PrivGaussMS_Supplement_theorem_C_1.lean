-- Prove2me | Theorems.Thm_PrivGaussMS_Supplement_theorem_C_1
-- name    : PrivGaussMS.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:20:20.517828+00:00
-- url     : https://prove2.me/theorems/706c4a4c-1a11-4964-a2a6-9e358a007fc4
-- title:
--   Theorem C.1 — lower bound $n \ge c\beta^3[m + \min\{d\sqrt m/(a_\beta(\varepsilon+\delta L_\delta)), m/(\delta L_\delta)\}]$ and $n \ge \beta^3 m/8$ for private Gaussian multi-sampling
-- statement:
--   This is the lower bound of the paper, matching the upper bound of Theorem B.1 up to logarithmic factors.
--
--   A **mechanism** $M$ takes a dataset of $n$ records in $\mathbb R^d$ and releases a batch of $m$ vectors in $\mathbb R^d$; it is a measurable randomized map $(\mathbb R^d)^n \to (\mathbb R^d)^m$. Two datasets are **neighbouring** if they differ by replacing one record, and $M$ is **$(\varepsilon,\delta)$-differentially private** if $\Pr\{M(x)\in E\} \le e^{\varepsilon}\Pr\{M(x')\in E\} + \delta$ for every fixed neighbouring pair $x, x'$ and every measurable event $E$. For a distribution $P$ on $\mathbb R^d$, write $P^{\otimes r}$ for the law of $r$ independent draws from $P$, and $M(P^{\otimes n})$ for the law of the released batch when the input has law $P^{\otimes n}$ (averaging over both the data and the mechanism's coins). The total variation distance is $\mathrm{TV}(P,Q) = \sup_E |P(E) - Q(E)|$ over measurable events.
--
--   There is a universal constant $c > 0$ with the following property. Let $d, m, n \ge 1$ be integers, $0 \le \alpha < 1$, $0 \le \varepsilon \le 1$ and $0 < \delta < 1$. Suppose $M$ is $(\varepsilon,\delta)$-differentially private and
--   $$
--   \mathrm{TV}\big(M(P^{\otimes n}), P^{\otimes m}\big) \le \alpha
--   $$
--   for every Gaussian distribution $P = \mathcal N(\mu, \Sigma)$ with $\mu \in \mathbb R^d$ arbitrary and $\Sigma \succ 0$. Set $\beta = 1 - \alpha$, $a_\beta = \sqrt{2\log(8/\beta)}$ and $L_\delta = \log(128/\delta)$ (natural logarithms). Then
--   $$
--   n \ge c\,\beta^3\left[m + \min\left\{\frac{d\sqrt m}{a_\beta(\varepsilon + \delta L_\delta)},\ \frac{m}{\delta L_\delta}\right\}\right] \qquad (45)
--   $$
--   and, in addition,
--   $$
--   n \ge \frac{\beta^3 m}{8}.
--   $$
--
--   The released vectors may be dependent: accuracy is only required for the joint law of the whole batch. No relation between $\delta$ and $n$ is assumed. For fixed $\alpha$ the bound reads $n = \widetilde\Omega_\alpha\big(m + \min\{d\sqrt m/(\varepsilon+\delta),\, m/\delta\}\big)$, which shows that the sample size of Theorem B.1 is optimal up to logarithmic factors.
--
--   **Formalization Note** The mechanism is a Markov kernel from datasets $\mathrm{Fin}\,n \to \mathbb R^d$ to batches $\mathrm{Fin}\,m \to \mathbb R^d$ (product Borel σ-algebras); $M(P^{\otimes n})$ is the composition of $P^{\otimes n}$ with this kernel. Privacy is the mission's `IsDPM`, built on the published replacement-neighbour definition of $(\varepsilon,\delta)$-DP, and TV is the published supremum over measurable sets. The constant $c$ is quantified before every other variable. Under the stated ranges all three denominators are strictly positive.
--
--   Differences from the source:
--   - encoding: a measurable randomized mechanism $M : (\mathbb R^d)^n \to (\mathbb R^d)^m$ → a Markov kernel `κ : Kernel (Fin n → Vec d) (Fin m → Vec d)` with `IsMarkovKernel κ`; reason: a Markov kernel is the law-level description of a measurable randomized map, and only output laws enter the statement (privacy and accuracy are both conditions on laws).
--   - encoding: $M(P^{\otimes n})$, the output law on input $X \sim P^{\otimes n}$ → `(Measure.pi fun _ : Fin n => multivariateGaussian μ Sig).bind κ`; reason: the bind is the law of the output averaged over the input and the mechanism's coins, as the source defines it.
--   - encoding: $(\varepsilon,\delta)$-DP and $\mathrm{TV}$ → the base `IsDPM` (which also records that each output law is a probability measure, automatic for a Markov kernel) and the published `tvDist` (a real supremum over measurable sets); reason: same definitions as on pp.62–63; no condition is added.
--   - encoding: $\mathcal N(\mu,\Sigma)$ with $\Sigma \succ 0$ → `multivariateGaussian μ Sig` with `Sig.PosDef`, `μ : EuclideanSpace ℝ (Fin d)`; reason: Mathlib's Gaussian with mean $\mu$ and covariance $\Sigma$; every mean and every positive definite covariance is covered.
--   - encoding: records $1,\dots,n$ and outputs $1,\dots,m$ → indices in `Fin n`, `Fin m`; reason: 0-based relabelling, no instance changes.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Theorem C.1, p.63, eq. (45) (setting and notation of Appendix C, pp.62–63; body version Theorem 4.1, p.14; informal version Theorem 1.2, p.4)

import Mathlib
import Definitions.Def_PrivGaussMS_Basics
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

namespace Supplement

/-- **Theorem C.1** (lower bound for private Gaussian multi-sampling).
R. Z. Moayedi, M. H. Yassaee, J. B. Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027
submission (manuscript sha256 1838c582…), Theorem C.1, p.63 (setting and notation of Appendix C,
pp.62–63); its body version is Theorem 4.1 (p.14) and its informal version Theorem 1.2 (p.4).

There is a universal constant `c > 0` such that for all integers `d, m, n ≥ 1`, all `0 ≤ α < 1`,
`0 ≤ ε ≤ 1` and `0 < δ < 1`, and every measurable randomized mechanism
`M : (ℝ^d)^n → (ℝ^d)^m` that is `(ε, δ)`-differentially private and satisfies
`TV(M(P^{⊗n}), P^{⊗m}) ≤ α` for every Gaussian `P = N(µ, Σ)` with `Σ ≻ 0`, writing
`β = 1 − α`, `a_β = √(2 log(8/β))`, `L_δ = log(128/δ)`:

* `n ≥ c β³ [m + min{d√m / (a_β (ε + δ L_δ)), m / (δ L_δ)}]` (eq. (45)), and
* `n ≥ β³ m / 8`.

**Formalization Note.**
* The mechanism is a Markov kernel `κ` from datasets `Fin n → Vec d` to output batches
  `Fin m → Vec d` (both with the product Borel σ-algebra). A Markov kernel is exactly a
  measurable randomized map; its measurability in the dataset is part of the `Kernel` structure.
  No independence, identical distribution or exchangeability of the `m` outputs is assumed.
* `M(P^{⊗n})` is the law of the output when the input has law `P^{⊗n}`, i.e. the composition
  `(P^{⊗n}).bind κ`; it averages over the input and the mechanism's coins together.
* Privacy is the base `IsDPM` (replacement neighbours, every fixed neighbouring pair of datasets,
  every measurable event); it carries no sign condition on `ε`, so `ε = 0` is covered.
* `TV` is the published `FoundationsRL.DECLower.tvDist`, the supremum of `|P(E) − Q(E)|` over
  measurable events; both arguments here are probability measures.
* `N(µ, Σ)` is Mathlib's `multivariateGaussian µ Σ`; accuracy is required for every mean
  `µ ∈ ℝ^d` and every positive definite `Σ` (`Matrix.PosDef`).
* `c` is quantified first, so it does not depend on `d, m, n, α, ε, δ` or the mechanism. All
  logarithms are natural (`Real.log`). Under the stated ranges `a_β > 0`, `ε + δ L_δ > 0` and
  `δ L_δ > 0`, so neither division is by zero. -/
theorem theorem_C_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d m n : ℕ), 1 ≤ d → 1 ≤ m → 1 ≤ n →
      ∀ (α ε δ : ℝ), 0 ≤ α → α < 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∀ (κ : Kernel (Fin n → Vec d) (Fin m → Vec d)), IsMarkovKernel κ →
        IsDPM (fun x : Fin n → Vec d => κ x) ε δ →
        (∀ (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ), Sig.PosDef →
          FoundationsRL.DECLower.tvDist
            ((Measure.pi fun _ : Fin n => multivariateGaussian μ Sig).bind κ)
            (Measure.pi fun _ : Fin m => multivariateGaussian μ Sig) ≤ α) →
        c * (1 - α) ^ 3 *
            ((m : ℝ) + min
              ((d : ℝ) * Real.sqrt (m : ℝ) /
                (Real.sqrt (2 * Real.log (8 / (1 - α))) * (ε + δ * Real.log (128 / δ))))
              ((m : ℝ) / (δ * Real.log (128 / δ)))) ≤ (n : ℝ) ∧
        (1 - α) ^ 3 * (m : ℝ) / 8 ≤ (n : ℝ) := by sorry

end Supplement

end PrivGaussMS
