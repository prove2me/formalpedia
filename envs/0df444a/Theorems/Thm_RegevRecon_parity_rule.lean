-- Prove2me | Theorems.Thm_RegevRecon_parity_rule
-- name    : RegevRecon.parity_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:17.602325+00:00
-- url     : https://prove2.me/theorems/716a57d7-89eb-41df-b97c-ecca556b4c3e
-- title:
--   (31)–(32) — the parity rule
-- statement:
--   With $V_{\mathrm{par}}|a,b\rangle=|a,b-a\rangle$, for all $d_1,d_2$,
--
--   $$
--   V_{\mathrm{par}}\bigl(|\phi_{d_1}(\mu)\rangle\otimes|\phi_{d_2}(\nu)\rangle\bigr)=\sum_s\omega^{-sd_2}\Bigl(\sum_a\sqrt{\mu_a\nu_{a+s}}\,\omega^{-a(d_1+d_2)}|a\rangle\Bigr)|s\rangle,
--   $$
--
--   and the $s$-component is $\sqrt{\pi_s}\,\omega^{-sd_2}|\phi_{d_1+d_2}(\mu^{(s)})\rangle|s\rangle$, with $\pi_s=\sum_a\mu_a\nu_{a+s}$ and $\mu_a^{(s)}=\mu_a\nu_{a+s}/\pi_s$. Thus measuring the second qudit gives a message about $d_1+d_2$, with a heralded classical label.
--
--   Differences from the source: none.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (31)–(32), p.11

import Mathlib
import Definitions.Def_RegevRecon_BPQMUnitaries

namespace RegevRecon

/-- **The parity rule (31)–(32)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.11: with `V_par |a, b⟩ = |a, b − a⟩`,
`V_par (|ϕ_{d1}(μ)⟩ ⊗ |ϕ_{d2}(ν)⟩) = Σ_s ω^{−s d2} (Σ_a √(μ_a ν_{a+s}) ω^{−a(d1+d2)} |a⟩) |s⟩`, and its
`s`-component is `√π_s ω^{−s d2} |ϕ_{d1+d2}(μ^(s))⟩ |s⟩` with `π_s, μ^(s)` of (32), for all `d1, d2`. -/
theorem parity_rule {p : ℕ} [Fact p.Prime] (μ ν : Vec p) (hμ : IsProbVec μ) (hν : IsProbVec ν)
    (d₁ d₂ : ZMod p) :
    (Vpar : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ) ∈ Matrix.unitaryGroup _ ℂ ∧
      (∀ a s : ZMod p,
        qditAct Vpar (qditTensor (messageState μ d₁) (messageState ν d₂)) (a, s) =
          zeta (-(s * d₂)) * (((Real.sqrt (μ a * ν (a + s)) : ℝ) : ℂ) * zeta (-(a * (d₁ + d₂))))) ∧
      ∀ a s : ZMod p,
        qditAct Vpar (qditTensor (messageState μ d₁) (messageState ν d₂)) (a, s) =
          ((Real.sqrt (parityProb μ ν s) : ℝ) : ℂ) * zeta (-(s * d₂)) *
            messageState (parityVec μ ν s) (d₁ + d₂) a := by sorry

end RegevRecon
