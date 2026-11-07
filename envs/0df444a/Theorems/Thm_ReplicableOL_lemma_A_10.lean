-- Prove2me | Theorems.Thm_ReplicableOL_lemma_A_10
-- name    : ReplicableOL.lemma_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:07.251131+00:00
-- url     : https://prove2.me/theorems/1739486b-463c-4e77-a3c2-f406e960741c
-- title:
--   Lemma A.10 — 0/1-valued rules
-- statement:
--   Let $\mu\sim U[-\Delta,\Delta]$ with $\Delta\in(0,\frac14]$, let $f:\{0,1\}^L\to\{0,1\}$, $q=q_f$, $d_f=\mathbb E|f(S)-f(S')|$ and $\mathrm{Cov}_f=\mathbb E[\mu f(S)]$. Then $d_f=2\mathbb E[q(\mu)(1-q(\mu))]$ and $|\mathrm{Cov}_f|\le\Delta/4$. Moreover:
--
--   1. (No crossing.) If $q\le\frac12$ on all of $[-\Delta,\Delta]$, or $q\ge\frac12$ on all of $[-\Delta,\Delta]$, then $|\mathrm{Cov}_f|\le\Delta d_f$ and $\mathrm{Var}(f(S))\le d_f$.
--   2. (Ambiguity interval.) If $q(\mu_0)=\frac12$ for some $\mu_0\in[-\Delta,\Delta]$, then
--   $$
--   d_f\ge\frac{3}{16\Delta}\min\Big\{\frac1{4\beta_L},\Delta\Big\},
--   $$
--   which is $3\sqrt3/(128\Delta\sqrt L)$ in the regime $\Delta\sqrt L\ge\sqrt3/8$.
--   3. In all cases $|\mathrm{Cov}_f|\le C(\Delta,L)d_f$ and $\mathrm{Var}(f(S))\le C_V(\Delta,L)d_f$.
--
--   This is the fixed-rule core of the gain-weighted coin lemma.
--
--   Differences from the source:
--   - encoding: $f:\{0,1\}^L\to\{0,1\}$ → $f:\{0,1\}^L\to\mathbb R$ with values in $\{0,1\}$; reason: same functions; the type is shared with Lemma A.8
--   - encoding: "which is $3\sqrt3/(128\Delta\sqrt L)$ in the regime" → an equality of the printed bound with that value, under $\sqrt3/8\le\Delta\sqrt L$; reason: that is what the sentence says
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma A.10, pp.29–30

import Mathlib
import Definitions.Def_ReplicableOL_uniformPrior
import Definitions.Def_ReplicableOL_Block
import Definitions.Def_ReplicableOL_qf
import Definitions.Def_ReplicableOL_betaL
import Definitions.Def_ReplicableOL_CDL
import Definitions.Def_ReplicableOL_CVDL
import Definitions.Def_ReplicableOL_covF
import Definitions.Def_ReplicableOL_dF
import Definitions.Def_ReplicableOL_varF
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma A.10.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma A.10, pp.29–30. All clauses.

**Formalization Note.** `f` takes values in `{0, 1}` as a real-valued function, so that `qf`, `covF`, `dF`, `varF` are shared with fractional rules. At `L = 0` the hypothesis of (b) cannot hold, so Lean's `1/(4·0) = 0` is not read. -/
theorem lemma_A_10 {L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (f : Block L → ℝ)
    (hf : ∀ s, f s = 0 ∨ f s = 1) :
    dF Δ f = 2 * ∫ μ, qf f μ * (1 - qf f μ) ∂(uniformPrior Δ) ∧
    |covF Δ f| ≤ Δ / 4 ∧
    (((∀ μ ∈ Set.Icc (-Δ) Δ, qf f μ ≤ 1 / 2) ∨ (∀ μ ∈ Set.Icc (-Δ) Δ, 1 / 2 ≤ qf f μ)) →
      |covF Δ f| ≤ Δ * dF Δ f ∧ varF Δ f ≤ dF Δ f) ∧
    ((∃ μ₀ ∈ Set.Icc (-Δ) Δ, qf f μ₀ = 1 / 2) →
      3 / (16 * Δ) * min (1 / (4 * betaL L)) Δ ≤ dF Δ f) ∧
    (√3 / 8 ≤ Δ * √(L : ℝ) →
      3 / (16 * Δ) * min (1 / (4 * betaL L)) Δ = 3 * √3 / (128 * Δ * √(L : ℝ))) ∧
    |covF Δ f| ≤ CDL Δ L * dF Δ f ∧ varF Δ f ≤ CVDL Δ L * dF Δ f := by sorry

end ReplicableOL
