-- Prove2me | Theorems.Thm_RandKSATSample_Main_theorem_4_1
-- name    : RandKSATSample.Main.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:01:17.759031+00:00
-- url     : https://prove2.me/theorems/bd1fc7d8-c713-426d-8aee-f492ff745c24
-- title:
--   Theorem 4.1 — spectral gap of the core heat bath: Var ≤ 2n^{γ_mix} Σ_j V_j, gap(K) ≥ 1/(2sn^{γ_mix}) ≥ 1/(2n^{1+γ_mix}), and the TV bound (4.11)
-- statement:
--   Suppose $n\ge2$ and $k\ge30$, with the parameters (4.4), and assume (4.1), (4.5), (4.6), (4.7), (4.8). Let $c_k=1-\frac{25}{3k^3}$, $\rho_0=\rho e^{-2\tau}$, $\gamma_{\mathrm{mix}}=64\rho_0/c_k$ (4.9). If $s\ge1$, then for every $f:\Omega\to\mathbb R$
--   $$\mathrm{Var}_{\mu^{\mathrm{bad}}}(f)\le2n^{\gamma_{\mathrm{mix}}}\sum_{j=1}^sV_j^{\mu^{\mathrm{bad}}}(f),\qquad\mathrm{gap}(\mathcal K)\ge\frac1{2sn^{\gamma_{\mathrm{mix}}}}\ge\frac1{2n^{1+\gamma_{\mathrm{mix}}}}\quad(4.10),$$
--   and for every $\sigma_0\in\Omega$ and integer $t\ge0$,
--   $$\big\|\mathcal K^t(\sigma_0,\cdot)-\mu^{\mathrm{bad}}\big\|_{TV}\le\frac12\,2^{n/2}\exp\Big(-\frac t{2sn^{\gamma_{\mathrm{mix}}}}\Big)\quad(4.11).$$
--   The block heat bath on the core mixes in polynomially many steps, which is the main ingredient of the running time of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: (4.5): |W_J| ≤ (k/2)|W_J ∩ V_high| and ∀ v ∈ V_high, deg(v) ≥ ∆ → Cond45 (the first clause); reason: the second clause is the definition of V_high
--   - encoding: functions f : Ω → ℝ and laws on Ω → functions on all assignments of V_bad, laws vanishing off Ω; reason: µbad is zero off Ω and the kernel moves only to states of positive µbad, so values off Ω do not enter any weighted sum
--   - encoding: ‖·‖_TV of (2.1) → IsingLTL.BeliefProp.tvDist (½ ℓ¹) over all assignments of V_bad; reason: both laws vanish off Ω
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 22, Theorem 4.1

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure
import Definitions.Def_RandKSATSample_Main_FiniteInteraction
import Definitions.Def_RandKSATSample_Main_CoreChain
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Theorem 4.1 (spectral gap of the core heat bath): for `n ≥ 2`, `k ≥ 30`, under (4.1),
(4.5)–(4.8) and `s ≥ 1`: `Var_{µbad}(f) ≤ 2 n^{γ_mix} Σ_j V_j^{µbad}(f)` for every `f`,
`gap(K) ≥ 1/(2 s n^{γ_mix}) ≥ 1/(2 n^{1+γ_mix})` (4.10), and for every `σ0 ∈ Ω` and `t ≥ 0`,
`‖K^t(σ0, ·) − µbad‖_TV ≤ ½ 2^{n/2} exp(−t/(2 s n^{γ_mix}))` (4.11). -/
theorem theorem_4_1 {n m k : ℕ} (Φ : Formula n m k) (hn : 2 ≤ n) (hk : 30 ≤ k)
    (h41 : Cond41 Φ) (h45 : Cond45 Φ) (h46 : Cond46 Φ) (h47 : Cond47 Φ) (h48 : Cond48 Φ)
    (hs : 1 ≤ (blocks Φ).card) :
    (∀ f : BadAssign Φ → ℝ,
      variance (muBad Φ) f ≤
        2 * (n : ℝ) ^ gammaMix n m k * ∑ B : Blk Φ, condVarAvg (muBad Φ) f (AgreeOutside Φ B.1)) ∧
    1 / (2 * ((blocks Φ).card : ℝ) * (n : ℝ) ^ gammaMix n m k) ≤ gapK Φ ∧
    1 / (2 * (n : ℝ) ^ (1 + gammaMix n m k)) ≤
      1 / (2 * ((blocks Φ).card : ℝ) * (n : ℝ) ^ gammaMix n m k) ∧
    ∀ σ0 ∈ Omega Φ, ∀ t : ℕ,
      IsingLTL.BeliefProp.tvDist (heatBathPow Φ t σ0) (muBad Φ) ≤
        1 / 2 * (2 : ℝ) ^ ((n : ℝ) / 2) *
          Real.exp (-(t : ℝ) / (2 * ((blocks Φ).card : ℝ) * (n : ℝ) ^ gammaMix n m k)) := by sorry

end RandKSATSample.Main
