-- Prove2me | Theorems.Thm_SupermodDRO_max_mad
-- name    : SupermodDRO.max_mad
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:07.741467+00:00
-- url     : https://prove2.me/theorems/d22ace84-7f01-4095-baa6-c5bfc1777fe6
-- title:
--   Proof of Proposition 1, p.40 — the maximum MAD on $[\underline z_i,\overline z_i]$ with mean $\mu_i$ (Ben-Tal–Hochman)
-- statement:
--   Let $\underline z<\overline z$ and $\mu\in[\underline z,\overline z]$. For every Borel probability distribution $\mathbb P$ on $\mathbb R$ with $\mathbb P([\underline z,\overline z])=1$ and mean $\mu$,
--   $$
--   \mathbb E_{\mathbb P}|\tilde z-\mu|\ \le\ \frac{2(\overline z-\mu)(\mu-\underline z)}{\overline z-\underline z},
--   $$
--   and some such distribution attains equality.
--
--   This bound is why the paper replaces $\delta_i$ by $\hat\delta_i=\min\{\delta_i,\,2(\overline z_i-\mu_i)(\mu_i-\underline z_i)/(\overline z_i-\underline z_i)\}$ in (5).
--
--   Differences from the source:
--   - reading: given the support [z̲ᵢ, z̄ᵢ] and mean µᵢ → hypothesis µ ∈ [z̲, z̄]; reason: a distribution on [z̲, z̄] has its mean there; the paper's implicit assumption
--   - encoding: the maximum possible value of MAD is 2(z̄ᵢ−µᵢ)(µᵢ−z̲ᵢ)/(z̄ᵢ−z̲ᵢ) → every feasible distribution has MAD at most this value and one attains it; reason: this is what maximum means
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proof of Proposition 1 (App. C.1), p.40 (citing Ben-Tal & Hochman 1972, Lemma 1)

import Mathlib

open MeasureTheory

namespace SupermodDRO

/-- **The maximum mean absolute deviation on an interval (Ben-Tal & Hochman 1972, Lemma 1).**
Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally Robust Optimization*, author
manuscript (June 2022), Proof of Proposition 1 (App. C.1), p.40: "For the i-th marginal, given the
support [z̲ᵢ, z̄ᵢ] and mean µᵢ, the maximum possible value of MAD is 2(z̄ᵢ − µᵢ)(µᵢ − z̲ᵢ)/(z̄ᵢ − z̲ᵢ)
(see Ben-Tal and Hochman (1972, Lemma 1))."

Let `zl < zu` and `μ ∈ [zl, zu]`. Every Borel probability measure `P` on `ℝ` with `P([zl, zu]) = 1`
and mean `μ` has `∫ |z − μ| dP ≤ 2(zu − μ)(μ − zl)/(zu − zl)`, and some such measure attains it.

**Formalization Note** "Maximum" is stated as the bound together with its attainment. The
condition `μ ∈ [zl, zu]` is the paper's implicit assumption that the support contains the mean. -/
theorem max_mad (zl zu μ : ℝ) (hlt : zl < zu) (hμ : μ ∈ Set.Icc zl zu) :
    (∀ P : Measure ℝ, IsProbabilityMeasure P → P (Set.Icc zl zu) = 1 → ∫ z, z ∂P = μ →
      ∫ z, |z - μ| ∂P ≤ 2 * (zu - μ) * (μ - zl) / (zu - zl)) ∧
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Set.Icc zl zu) = 1 ∧ ∫ z, z ∂P = μ ∧
      ∫ z, |z - μ| ∂P = 2 * (zu - μ) * (μ - zl) / (zu - zl) := by sorry

end SupermodDRO
