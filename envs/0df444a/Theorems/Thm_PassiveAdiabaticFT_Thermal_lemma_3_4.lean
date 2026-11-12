-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_lemma_3_4
-- name    : PassiveAdiabaticFT.Thermal.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:46.995202+00:00
-- url     : https://prove2.me/theorems/1e92677b-af11-4dea-bcb8-b7a61d2d167b
-- title:
--   Lemma 3.4 — the comparison chain stays below the bath Gibbs weights
-- statement:
--   Consider a single code block with penalty $J>0$, let $\beta'\ge\beta$, $q_0=\pi_{\beta'}$ and $q_t=e^{t\sum_\alpha\mathsf M_\alpha}q_0$, where $\mathsf M_\alpha$ is the classical generator (3.7) of one block with rates $\gamma_\alpha^{(\omega)}\ge0$ satisfying detailed balance $\gamma_\alpha^{(-\omega)}=e^{-\beta\omega}\gamma_\alpha^{(\omega)}$ for $\omega>0$. Then for every $s\in\Omega$ and every $t\ge0$,
--   $$q_t(s)\le\frac{Z_1(\beta)}{Z_1(\beta')}\,\pi_\beta(s).\qquad(3.28)$$
--
--   Starting colder than the bath never puts more than a factor $Z_1(\beta)/Z_1(\beta')$ of the bath's Gibbs weight on any syndrome; this is what allows initial states at or below the bath temperature.
--
--   Differences from the source:
--   - generalization: rates of the noise model (1.18)–(1.19) → only nonnegativity and detailed balance (1.18) at β; reason: the proof uses only these; the bounds γ, κ of (1.19) are not needed
--   - encoding: q_t = e^{Σ_α M_α t} q_0 → the real matrix exponential exp(t • Σ_α M_α) applied to q_0 as a vector on Ω; reason: the same linear evolution
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 24, Lemma 3.4 (3.28)–(3.30)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Blocks

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Lemma 3.4 (p. 24): for a single code block, `q_0 = π_{β'}` with `β' ≥ β`, and
`q_t = e^{t Σ_α M_α} q_0`, one has `q_t(s) ≤ (Z_1(β)/Z_1(β')) π_β(s)` for all `s ∈ Ω`, `t ≥ 0`,
when the rates are nonnegative and satisfy detailed balance (1.18) at `β`. -/
theorem lemma_3_4 {b : ℕ} (C : StabCode b) (D : PauliDecoder C) (J : ℝ) (hJ : 0 < J)
    (β β' : ℝ) (hβ : β ≤ β') (γr : Fin b × Fin 3 → ℝ → ℝ) (hnn : ∀ a ω, 0 ≤ γr a ω)
    (hdb : ∀ a ω, 0 < ω → γr a (-ω) = Real.exp (-(β * ω)) * γr a ω)
    (t : ℝ) (ht : 0 ≤ t) (s : C.Om) :
    (NormedSpace.exp (t • ∑ a, D.Mblock J a (γr a)) *ᵥ fun s' : C.Om => C.gibbs J β' s'.1) s ≤
      C.Z J β / C.Z J β' * C.gibbs J β s.1 := by sorry

end PassiveAdiabaticFT.Thermal
