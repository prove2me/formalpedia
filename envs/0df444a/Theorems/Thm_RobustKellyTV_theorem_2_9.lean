-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_2_9
-- name    : RobustKellyTV.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:18.129203+00:00
-- url     : https://prove2.me/theorems/77816150-294e-4d70-bc44-3b3c4f57eff8
-- title:
--   Theorem 2.9 — universal information lower bound $\mathbb E_S\tau\ge\log(1/\alpha)/\Gamma(S)$
-- statement:
--   Assume the standing assumptions. Fix a full-support $S\in\Delta_d\setminus\mathcal P_0$ and a level $\alpha\in(0,1)$, and let $\tau$ be any stopping time for the filtration $\mathcal F_n=\sigma(X_1,\dots,X_n)$ (values in $\mathbb N\cup\{\infty\}$) with
--
--   $$\sup_{R\in\mathcal P_0}P_R(\tau<\infty)\le\alpha,\qquad P_S(\tau<\infty)=1,$$
--
--   where $P_R$ is the i.i.d. law with marginal $R$. Then
--
--   $$\mathbb E_S\tau\ge\frac{\log(1/\alpha)}{\Gamma(S)} .$$
--
--   No level-$\alpha$ power-one test can stop faster in expectation than the oracle rate.
--
--   Differences from the source:
--   - encoding: τ any stopping rule; E_S τ → τ : (ℕ → Fin d) → ℕ∞ a stopping time for the prefix filtration; E_S τ as a lintegral in [0, ∞]; reason: the sequential-testing setting of §1.1
--   - reading: level α → α ∈ (0, 1); reason: the levels considered by the paper (p.2)
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.3, Theorem 2.9, eq. (22), p.10 (proof p.27)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Theorem 2.9** (Universal information lower bound). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 2.9, eq. (22), p.10.

Fix a full-support `S ∉ P0`, and let `τ` be any stopping rule satisfying
`sup_{R ∈ P0} P_R(τ < ∞) ≤ α` and `P_S(τ < ∞) = 1`. Then `E_S τ ≥ log(1/α)/Γ(S)`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `τ` is a stopping time for the prefix filtration on `ℕ → Fin d`,
valued in `ℕ∞`; `E_S τ` is a `lintegral` in `[0, ∞]`. `P_R` is the i.i.d. law with marginal `R`;
the supremum bound is required for every `R ∈ P0`. The level is `α ∈ (0, 1)` (p.2). The paper's
`R_S` names the reverse projection used in the proof; it does not enter the statement. -/
theorem theorem_2_9 {d : ℕ} (σ : Setting d) (S : stdSimplex ℝ (Fin d))
    (hSP : (S : Fin d → ℝ) ∉ nullBall σ) (hSpos : ∀ i, 0 < (S : Fin d → ℝ) i)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (τ : (ℕ → Fin d) → ℕ∞)
    (hτ : IsStoppingTime (prefixFiltration d) τ)
    (hlevel : ∀ (R : Fin d → ℝ) (hR : R ∈ nullBall σ),
      seqLaw ⟨R, hR.1⟩ {ω | τ ω < ⊤} ≤ ENNReal.ofReal α)
    (hpow : seqLaw S {ω | τ ω < ⊤} = 1) :
    ENNReal.ofReal (Real.log (1 / α) / Gamma σ S) ≤ ∫⁻ ω, (τ ω : ℝ≥0∞) ∂(seqLaw S) := by sorry

end RobustKellyTV
