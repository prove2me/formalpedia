-- Prove2me | Theorems.Thm_SmoothNestedSim_lemma_EC_2
-- name    : SmoothNestedSim.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:11.413187+00:00
-- url     : https://prove2.me/theorems/37d5bcae-daf6-4de4-9b50-85b9879a1e50
-- title:
--   Lemma EC.2: zero-mean $Z_n$ with finite variance satisfy $Z_n=O_{\mathbb P}(\sqrt{\mathrm{Var}(Z_n)})$
-- statement:
--   Let $(Z_k)$ be real random variables, $Z_k$ defined on a probability space $(S_k,P_k)$, each with mean zero and finite variance. Then
--
--   $$
--   |Z_k| = O_{\mathbb P}\Bigl(\sqrt{\mathrm{Var}(Z_k)}\Bigr),
--   $$
--
--   in the sense of $O_{\mathbb P}$ of p.8: for every $\varepsilon>0$ there is $C>0$ with $P_k(|Z_k|>C\sqrt{\mathrm{Var}(Z_k)})<\varepsilon$ for all $k$ large enough.
--
--   The lemma (Theorem 14.4-1 in Bishop, Fienberg and Holland, 2007) converts the variance bounds of the proof of Proposition 1 into rates in probability.
--
--   **Formalization Note** Finite variance is membership in $L^2$.
--
--   Differences from the source:
--   - reading: Zₙ = O_ℙ(√Var(Zₙ)) for a signed sequence → |Z_k| = O_ℙ(√Var(Z_k)); reason: O_ℙ of p.8 is stated for positive sequences; the absolute value is the usual meaning and implies the one-sided bound
--   - generalization: Z₁, …, Zₙ random variables (on one space) → Z_k on its own probability space (S_k, P_k) for each k; reason: one fixed space is the constant family
--   - encoding: Var(Zᵢ) < ∞ → MemLp (Z k) 2 (P k); reason: a measurable variable has finite variance iff it is in L²
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, Lemma EC.2, p.ec9 (PDF p.55)

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP

open MeasureTheory ProbabilityTheory

namespace SmoothNestedSim

/-- **Lemma EC.2** (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6,
Lemma EC.2, p.ec9 = PDF p.55, citing Theorem 14.4-1 in Bishop et al. 2007): "Let `Z₁, …, Zₙ`
be zero-mean random variables such that `𝕍ar(Zᵢ) < ∞` for all `i = 1, …, n`. Then,
`Zₙ = O_ℙ(√𝕍ar(Zₙ))`."

For a sequence of real random variables `Z_k` on probability spaces `(S k, P k)`, each
square-integrable with mean zero, `|Z_k| = O_ℙ(√𝕍ar(Z_k))` in the sense of p.8.

**Formalization Note.** Finite variance is `MemLp (Z k) 2 (P k)` (which includes measurability).
`O_ℙ` is applied to `|Z_k|`, the usual meaning of `Z_n = O_ℙ(·)` for a signed sequence (it
implies the one-sided bound on `Z_k`). Each index may carry its own probability space; one fixed
space is the special case of a constant family. -/
theorem lemma_EC_2 {S : ℕ → Type*} [∀ k, MeasurableSpace (S k)] (P : ∀ k, Measure (S k))
    [∀ k, IsProbabilityMeasure (P k)] (Z : ∀ k, S k → ℝ) (hZ : ∀ k, MemLp (Z k) 2 (P k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂(P k) = 0) :
    IsBigOP P (fun k ω => |Z k ω|) (fun k => Real.sqrt (variance (Z k) (P k))) := by sorry

end SmoothNestedSim
