-- Prove2me | Theorems.Thm_RandPurIso_Completion_Supplement_theorem_7_1
-- name    : RandPurIso.Completion.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:55:14.945025+00:00
-- url     : https://prove2.me/theorems/616322c4-9499-42b9-bd18-e4c0c579fe95
-- title:
--   Theorem 7.1 — SAME/DIFF: one self-switch distinguishes, $q$ forward queries give advantage $O(q^{3/2}/D^{1/2})$
-- statement:
--   There is an absolute constant $C>0$ such that for every $D\ge3$ there are two ensembles of quantum channels $\mathsf{SAME}$ and $\mathsf{DIFF}$ with input and output dimension $D$ such that:
--
--   1. one application of the quantum switch to two copies of the same unknown channel distinguishes any pair from the supports perfectly: there is a state $\rho$ such that for all $\Phi_{\mathsf{SAME}}\in\mathsf{SAME}$, $\Phi_{\mathsf{DIFF}}\in\mathsf{DIFF}$,
--   $$
--   \mathrm{TD}\big(\mathrm{Sw}[\Phi_{\mathsf{SAME}},\Phi_{\mathsf{SAME}}](\rho),\ \mathrm{Sw}[\Phi_{\mathsf{DIFF}},\Phi_{\mathsf{DIFF}}](\rho)\big)=1;
--   $$
--   2. for every $q\ge1$ and every oracle algorithm $\mathcal A$ independent of the hidden randomness making at most $q$ forward channel queries,
--   $$
--   \mathrm{TD}\big(\mathbb E[\mathcal A^{\mathsf{SAME}}],\ \mathbb E[\mathcal A^{\mathsf{DIFF}}]\big)\le C\,\frac{q^{3/2}}{D^{1/2}},
--   $$
--   the expectations being over the hidden randomness, sampled once and fixed throughout each experiment. Consequently, if this trace distance is at least $\delta>0$ then $q\ge(\delta/C)^{2/3}D^{1/3}$: constant advantage needs $\Omega(D^{1/3})$ channel queries.
--
--   The theorem separates the quantum switch from forward channel access, and gives lower bounds for simulating the switch (Corollary 7.2) and random isometry dilations (Corollary 7.4).
--
--   **Formalization Note** An ensemble is a probability space $(\Omega,\mu)$ with, for each $\omega$, a Kraus family of $r$ operators on $\mathbb C^D$ satisfying $\sum K^\dagger K=I$. Clause 1 holds for every pair of parameter values. The integrands of clause 2 are required to be integrable (entrywise), so the Bochner integrals are genuine expectations. Algorithms are the base mission's `OracleAlg` (any finite workspace, any CPTP steps); a forward channel query is `chanOracle`.
--
--   Differences from the source:
--   - generalization: for every D, q there are ensembles SAME, DIFF (∀ D q ∃ ensembles) → for every D there are ensembles SAME, DIFF that work for every q ≥ 1 (∀ D ∃ ensembles ∀ q); reason: stronger and specializes to the page's order; the page's construction (L = ⌊(D−1)/2⌋, d = 2) does not depend on q, and the 'Consequently' sentence needs ensembles fixed before q
--   - reading: TD(E[A^SAME], E[A^DIFF]) = O(q^{3/2}/D^{1/2}), the implicit constant absolute; consequently constant advantage requires Ω(D^{1/3}) queries → ∃ C > 0 before D: TD ≤ C q^{3/2}/√D, and TD ≥ δ > 0 implies q ≥ (δ/C)^{2/3} D^{1/3}; reason: the page says the constant is absolute; the consequence is stated with the same constant
--   - encoding: ensembles of channels with input and output dimension D; 'for all Φ in the supports' → a probability space (Ω, μ) and Kraus families KS ω, KD ω : Fin r → Matrix (Fin D) (Fin D) ℂ with Σ K†K = 1; clause 1 for every pair ω, ω'; reason: the support of the law of a measurable family lies in the closure of its range and TD(Sw…) = 1 is a closed condition, so the clause for every parameter value gives it on the supports
--   - encoding: E[A^SAME], E[A^DIFF] over the hidden pairs → Bochner integrals ∫ A.run(chanOracle Φ_ω) dμ, with entrywise integrability of both integrands asserted; reason: rules out the junk value 0 of a non-integrable integral; same instances
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 7.1, p. 48

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_traceDist
import Definitions.Def_RandPurIso_Completion_Supplement_qswitch
import Definitions.Def_RandPurIso_Completion_Supplement_chanOracle
open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Theorem 7.1** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7, p. 48).

For every `D ≥ 3` there are two ensembles of quantum channels SAME and DIFF with input and output
dimension `D` such that (1) there is a state `ρ` with
`TD(Sw[Φ_SAME, Φ_SAME](ρ), Sw[Φ_DIFF, Φ_DIFF](ρ)) = 1` for all `Φ_SAME ∈ SAME`, `Φ_DIFF ∈ DIFF`; and
(2) for every `q ≥ 1` and every oracle algorithm `A` independent of the hidden pairs making at most
`q` forward channel queries, `TD(E[A^SAME], E[A^DIFF]) ≤ C q^{3/2} / D^{1/2}` with an absolute
constant `C`; consequently constant advantage `δ` needs `q ≥ (δ/C)^{2/3} D^{1/3}` queries.

**Formalization Note.**
* `O(·)`: one absolute `C > 0`, chosen before `D` and `q`.
* An ensemble is a probability space `(Ω, μ)` (the hidden randomness) and, for each `ω`, a Kraus
  family `KS ω` (resp. `KD ω`) of `r` operators on `ℂ^D` with `Σ K†K = 1`, i.e. a channel. SAME and
  DIFF share `Ω`, `μ`. Clause 1 is asserted for every pair `ω, ω'`, hence for every pair in the
  supports. Clause 2's expectations are Bochner integrals, and entrywise integrability of both
  integrands is part of the conclusion, so they are genuine expectations.
* The ensembles are chosen before `q` (the page writes "for every `D, q` there are ensembles"); a
  `q`-independent choice is stronger and is what makes the "Consequently" sentence meaningful.
* `A` is any oracle algorithm of the base mission with query register `ℂ^D`; a forward channel
  query is `chanOracle` of the channel `ρ ↦ Σ_j K_j ρ K_j†`. -/
theorem theorem_7_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 3 ≤ D →
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ) (_ : @IsProbabilityMeasure Ω mΩ μ)
        (r : ℕ) (KS KD : Ω → Fin r → Matrix (Fin D) (Fin D) ℂ),
        (∀ ω, ∑ j, (KS ω j)ᴴ * KS ω j = 1) ∧ (∀ ω, ∑ j, (KD ω j)ᴴ * KD ω j = 1) ∧
        (∃ ρ : Matrix (Bool × Fin D) (Bool × Fin D) ℂ, PeresTerno.IsDensityMatrix ρ ∧
          ∀ ω ω' : Ω, traceDist (qswitch (KS ω) (KS ω) ρ) (qswitch (KD ω') (KD ω') ρ) = 1) ∧
        ∀ q : ℕ, 1 ≤ q →
          ∀ (W : Type) [Fintype W] [DecidableEq W] (A : OracleAlg (Fin D) (Fin D) W),
            A.numQueries ≤ q →
            (∀ i j, Integrable (fun ω => A.run (chanOracle (PeresTerno.krausUpdate (KS ω))) i j) μ) ∧
            (∀ i j, Integrable (fun ω => A.run (chanOracle (PeresTerno.krausUpdate (KD ω))) i j) μ) ∧
            traceDist (∫ ω, A.run (chanOracle (PeresTerno.krausUpdate (KS ω))) ∂μ)
                (∫ ω, A.run (chanOracle (PeresTerno.krausUpdate (KD ω))) ∂μ) ≤
              C * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt D ∧
            ∀ δ : ℝ, 0 < δ →
              δ ≤ traceDist (∫ ω, A.run (chanOracle (PeresTerno.krausUpdate (KS ω))) ∂μ)
                (∫ ω, A.run (chanOracle (PeresTerno.krausUpdate (KD ω))) ∂μ) →
              (δ / C) ^ ((2 : ℝ) / 3) * (D : ℝ) ^ ((1 : ℝ) / 3) ≤ q := by sorry

end RandPurIso.Completion.Supplement
