-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_etilde_le
-- name    : QuantumWalkSearch.ApproxRAA.etilde_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:23.63399+00:00
-- url     : https://prove2.me/theorems/7d9a21cd-c859-4c03-9b1f-9fad81ececc8
-- title:
--   §4, p. 14 — the surrogate error satisfies ẽᵢ ≤ γϕ̄ᵢ/π ≤ γ for every i ≤ t
-- statement:
--   Let $\gamma>0$, $\phi_0\ge0$, $\bar\phi_i=3^i\phi_0$ and $\beta_i=\frac{18}{4\pi^3}\frac{\gamma}{i^2}$. Define the surrogate error by
--   $$
--   \tilde e_0=0,\qquad \tilde e_{i+1}=4\beta_{i+1}\bar\phi_i+3\tilde e_i .
--   $$
--   If $t$ is a non-negative integer with $\bar\phi_t\le\pi$, then for every $i\le t$
--   $$
--   \tilde e_i\le\frac{\gamma\,\bar\phi_i}{\pi}\le\gamma .
--   $$
--
--   The precisions $\beta_i$ are summable, $\sum_i\beta_i<3\gamma/(4\pi)$, so the errors injected at successive levels stay below $\gamma$ although every level triples the error already present. In the proof of Lemma 1 the bound is applied with $\phi_0=\sin^{-1}\sqrt{p_M}$ and $t$ the number of levels.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 14, §4 ("We show that ẽᵢ ≤ γ for every i ≤ t" and "ẽᵢ ≤ γϕ̄ᵢ/π ≤ γ since 0 ≤ ϕ̄_t ≤ π for i ≤ t")

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

namespace QuantumWalkSearch.ApproxRAA

/-- §4, p. 14: the surrogate error `ẽ_0 = 0`, `ẽ_{i+1} = 4 β_{i+1} ϕ̄_i + 3 ẽ_i`
(`ϕ̄_i = 3^i ϕ₀`, `β_i = 18γ/(4π³ i²)`) satisfies `ẽ_i ≤ γ ϕ̄_i / π ≤ γ` for every `i ≤ t`,
when `γ > 0` and `0 ≤ ϕ̄_t ≤ π`. -/
theorem etilde_le (γ φ₀ : ℝ) (hγ : 0 < γ) (hφ₀ : 0 ≤ φ₀) (t : ℕ)
    (ht : (3 : ℝ) ^ t * φ₀ ≤ Real.pi) (i : ℕ) (hi : i ≤ t) :
    etilde γ φ₀ i ≤ γ * ((3 : ℝ) ^ i * φ₀) / Real.pi ∧
      γ * ((3 : ℝ) ^ i * φ₀) / Real.pi ≤ γ := by sorry

end QuantumWalkSearch.ApproxRAA
