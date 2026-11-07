-- Prove2me | Theorems.Thm_RobustKellyTV_corollary_2_7
-- name    : RobustKellyTV.corollary_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:54.169105+00:00
-- url     : https://prove2.me/theorems/60f0b54d-f4a6-46b2-bebf-40f288ed1872
-- title:
--   Corollary 2.7 — expected regret $0\le n\Gamma(S)-\mathbb E_S\log M^{\mathrm{CK}}_n\le\log\binom{n+d-1}{d-1}$, (18) and (19)
-- statement:
--   Assume the standing assumptions, the Laplace pseudocounts, and that the observations are i.i.d. from a fixed full-support $S\in\Delta_d\setminus\mathcal P_0$. For every $n\ge1$, $\log M^{\mathrm{CK}}_n$ is integrable and
--
--   $$0\le n\Gamma(S)-\mathbb E_S\log M^{\mathrm{CK}}_n\le\log\binom{n+d-1}{d-1},\qquad n\Gamma(S)-\mathbb E_S\log M^{\mathrm{CK}}_n\le(d-1)\log\frac{e(n+d-1)}{d-1},$$
--
--   $$0\le\Gamma(S)-\frac1n\mathbb E_S\log M^{\mathrm{CK}}_n\le\frac1n\log\binom{n+d-1}{d-1}\longrightarrow0 .$$
--
--   The learning cost vanishes per observation: the process attains the oracle growth rate $\Gamma(S)$.
--
--   Differences from the source:
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
--   - encoding: E_S log M_n → the Bochner integral, with integrability of log M_n as an added conjunct; reason: the conjunct is true (log M_n is a bounded function of finitely many coordinates) and prevents a junk value 0
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.2, Corollary 2.7, eqs. (17)–(19), p.9

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Mck

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Corollary 2.7** (Expected regret and pointwise instance optimality). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Corollary 2.7,
eqs. (17)–(19), p.9.

Assume (16) and that the observations are i.i.d. from a fixed full-support `S ∈ ∆_d \ P0`. For
every `n ≥ 1`, `0 ≤ nΓ(S) − E_S log M^CK_n ≤ log C(n + d − 1, d − 1)` (17); consequently, for
`d ≥ 2`, `nΓ(S) − E_S log M^CK_n ≤ (d − 1) log(e(n + d − 1)/(d − 1))` (18); in particular
`0 ≤ Γ(S) − (1/n) E_S log M^CK_n ≤ (1/n) log C(n + d − 1, d − 1) → 0` (19).

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `E_S` is the Bochner integral under the i.i.d. law on `ℕ → Fin d`;
integrability of `log M^CK_n` is a conjunct, so a junk value `0` cannot make the bounds hold. The
limit in (19) is the last conjunct. -/
theorem corollary_2_7 {d : ℕ} (σ : Setting d) (S : stdSimplex ℝ (Fin d))
    (hSP : (S : Fin d → ℝ) ∉ nullBall σ) (hSpos : ∀ i, 0 < (S : Fin d → ℝ) i) :
    (∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.log (Mck σ (laplace d) n ω)) (seqLaw S) ∧
      0 ≤ n * Gamma σ S - ∫ ω, Real.log (Mck σ (laplace d) n ω) ∂(seqLaw S) ∧
      n * Gamma σ S - ∫ ω, Real.log (Mck σ (laplace d) n ω) ∂(seqLaw S) ≤
        Real.log ((Nat.choose (n + d - 1) (d - 1) : ℕ) : ℝ) ∧
      n * Gamma σ S - ∫ ω, Real.log (Mck σ (laplace d) n ω) ∂(seqLaw S) ≤
        ((d : ℝ) - 1) * Real.log (Real.exp 1 * ((n : ℝ) + d - 1) / ((d : ℝ) - 1)) ∧
      0 ≤ Gamma σ S - (1 / (n : ℝ)) * ∫ ω, Real.log (Mck σ (laplace d) n ω) ∂(seqLaw S) ∧
      Gamma σ S - (1 / (n : ℝ)) * ∫ ω, Real.log (Mck σ (laplace d) n ω) ∂(seqLaw S) ≤
        (1 / (n : ℝ)) * Real.log ((Nat.choose (n + d - 1) (d - 1) : ℕ) : ℝ)) ∧
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log ((Nat.choose (n + d - 1) (d - 1) : ℕ) : ℝ))
      atTop (𝓝 0) := by sorry

end RobustKellyTV
