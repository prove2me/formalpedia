-- Prove2me | Theorems.Thm_RobustKellyTV_corollary_3_3
-- name    : RobustKellyTV.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:39.674208+00:00
-- url     : https://prove2.me/theorems/da89e148-4d02-4e10-8b76-695f9240e07d
-- title:
--   Corollary 3.3 — exact Wald constant and optimal Farrell order for $M^{\mathrm{mix}}$
-- statement:
--   Assume the standing assumptions ($d\ge2$, $P_i>0$, $0<\epsilon_0<1-\min_iP_i$), and let $M^{\mathrm{mix}}=\tfrac12M^{\mathrm{CK}}+\tfrac12M^{\mathrm F}$ with Laplace pseudocounts. Then:
--
--   1. $M^{\mathrm{mix}}$ is an $\alpha$-independent test supermartingale under $\mathcal P_0$.
--   2. It has power one under every i.i.d. $S\in\Delta_d\setminus\mathcal P_0$: for every $\alpha\in(0,1)$, $P_S(\tau_\alpha(M^{\mathrm{mix}})<\infty)=1$.
--   3. For every full-support $S\notin\mathcal P_0$,
--   $$\mathbb E_S\tau_\alpha(M^{\mathrm{mix}})\sim\frac{\log(1/\alpha)}{\Gamma(S)}\quad\text{as }\alpha\downarrow0 .$$
--   4. There is $C'_{P,\epsilon_0,d}$ such that for every $S\notin\mathcal P_0$ with $0<\Gamma(S)\le1$ and every $\alpha\in(0,1)$,
--   $$\mathbb E_S\tau_\alpha(M^{\mathrm{mix}})\le\frac{C'_{P,\epsilon_0,d}}{\Gamma(S)}\Big[d+\log(1/\alpha)+\ell(\Gamma(S))\Big].$$
--   5. For every full-support $S\notin\mathcal P_0$ and every $n\ge1$, $\log M^{\mathrm{mix}}_n$ is integrable and
--   $$0\le n\Gamma(S)-\mathbb E_S\log M^{\mathrm{mix}}_n\le\log\binom{n+d-1}{d-1}+\log2 .$$
--
--   One sequential test is thus simultaneously optimal as $\alpha\downarrow0$ (exact Wald constant) and as $\Gamma(S)\downarrow0$ (Farrell order), with logarithmic expected regret.
--
--   Differences from the source:
--   - encoding: test supermartingale under P0 → M_0 = 1, M ≥ 0, and a supermartingale for the prefix filtration under every i.i.d. law R^∞ with R ∈ P0; reason: the paper's reading in the proofs of Theorems 2.5 and 3.2 (pp.23, 29)
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
--   - encoding: α-independent → M^mix takes no level argument; reason: holds by construction
--   - reading: power one under every i.i.d. S ∉ P0 → for every α ∈ (0,1), P_S(τ_α(M^mix) < ∞) = 1; reason: the definition of power one on p.4 (eventual rejection with probability one), at every level
--   - encoding: E_S τ → a lintegral of τ (valued in ℕ∞) in [0, ∞]; reason: an infinite expectation is kept as ∞ and cannot read as 0
--   - encoding: E_S τ ∼ log(1/α)/Γ(S) as α ↓ 0 → the [0, ∞]-valued ratio E_S τ / (log(1/α)/Γ(S)) tends to 1 as α → 0⁺; reason: the meaning of ∼; the ratio is not truncated
--   - encoding: E_S log M_n → the Bochner integral, with integrability of log M_n as an added conjunct; reason: the conjunct is true (log M_n is a bounded function of finitely many coordinates) and prevents a junk value 0
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §3.3, Corollary 3.3, eqs. (31)–(33), p.12 (proof p.31)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Mmix

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Corollary 3.3** (Exact Wald constant and optimal Farrell order). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Corollary 3.3,
eqs. (31)–(33), p.12.

The process `M^mix` is an `α`-independent test supermartingale under `P0` and is power one under
every i.i.d. `S ∉ P0`. For each fixed full-support `S ∉ P0`, `E_S τ_α(M^mix) ∼ log(1/α)/Γ(S)` as
`α ↓ 0` (31). For every `S ∉ P0` with `0 < Γ(S) ≤ 1`,
`E_S τ_α(M^mix) ≤ C′_{P,ϵ0,d}/Γ(S) [d + log(1/α) + ℓ(Γ(S))]` (32). Finally, for fixed full-support
`S ∉ P0`, `0 ≤ nΓ(S) − E_S log M^mix_n ≤ log C(n + d − 1, d − 1) + log 2` (33).

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. Five conjuncts.
1. Validity: `M^mix₀ = 1`, `M^mix ≥ 0`, and a supermartingale for the prefix filtration under every
   i.i.d. law `R^∞`, `R ∈ P0`. `M^mix` takes no level, which is the `α`-independence.
2. Power one: for every `S ∈ ∆_d \ P0` (zero coordinates allowed) and every level `α ∈ (0, 1)`,
   `τ_α(M^mix) < ∞` almost surely under the i.i.d. law of `S`.
3. (31): `E_S τ` is a `lintegral` in `[0, ∞]`, and `∼` is convergence of the `[0, ∞]`-valued ratio
   to `1` as `α → 0⁺`.
4. (32): the constant `C′` is chosen after the setting and before `S` and `α`.
5. (33): for every `n ≥ 1`, with integrability of `log M^mix_n` as a conjunct. -/
theorem corollary_3_3 {d : ℕ} (σ : Setting d) :
    IsTestSupermartingale σ (Mmix σ) ∧
    (∀ S : stdSimplex ℝ (Fin d), (S : Fin d → ℝ) ∉ nullBall σ → ∀ α : ℝ, 0 < α → α < 1 →
      seqLaw S {ω | stopTime (Mmix σ) α ω < ⊤} = 1) ∧
    (∀ S : stdSimplex ℝ (Fin d), (S : Fin d → ℝ) ∉ nullBall σ → (∀ i, 0 < (S : Fin d → ℝ) i) →
      Tendsto (fun α : ℝ =>
          (∫⁻ ω, (stopTime (Mmix σ) α ω : ℝ≥0∞) ∂(seqLaw S)) /
            ENNReal.ofReal (Real.log (1 / α) / Gamma σ S))
        (𝓝[>] 0) (𝓝 1)) ∧
    (∃ C' : ℝ, ∀ S : stdSimplex ℝ (Fin d), (S : Fin d → ℝ) ∉ nullBall σ →
      0 < Gamma σ S → Gamma σ S ≤ 1 → ∀ α : ℝ, 0 < α → α < 1 →
        ∫⁻ ω, (stopTime (Mmix σ) α ω : ℝ≥0∞) ∂(seqLaw S) ≤
          ENNReal.ofReal (C' / Gamma σ S *
            ((d : ℝ) + Real.log (1 / α) + ell (Gamma σ S)))) ∧
    (∀ S : stdSimplex ℝ (Fin d), (S : Fin d → ℝ) ∉ nullBall σ → (∀ i, 0 < (S : Fin d → ℝ) i) →
      ∀ n : ℕ, 1 ≤ n →
        Integrable (fun ω => Real.log (Mmix σ n ω)) (seqLaw S) ∧
        0 ≤ n * Gamma σ S - ∫ ω, Real.log (Mmix σ n ω) ∂(seqLaw S) ∧
        n * Gamma σ S - ∫ ω, Real.log (Mmix σ n ω) ∂(seqLaw S) ≤
          Real.log ((Nat.choose (n + d - 1) (d - 1) : ℕ) : ℝ) + Real.log 2) := by sorry

end RobustKellyTV
