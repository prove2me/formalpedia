-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_4_3
-- name    : RandKSATSample.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:01:06.845221+00:00
-- url     : https://prove2.me/theorems/bc273c3e-09bd-4e0e-904a-be7b8556f237
-- title:
--   Lemma 4.3 — cluster expansion ln Z(σ) = Σ_Γ a_Γ Y_Γ(σ), Σ_{Γ: a∈U_Γ} |a_Γ| e^{τK_Γ} ≤ ρ, and Σ_Γ sup_σ |a_Γ Y_Γ(σ)| ≤ mρ
-- statement:
--   Under (4.8) ($\tau\ge1$ and $\sum_{S\in\mathsf{CS}_\Psi(a)}q_Se^{(1+\tau)|S|}\le\rho$ for every good $a$), with §4's standing (4.7) ($|N_{H_\Psi}[a]|\le D$):
--   $$\ln Z(\sigma)=\sum_\Gamma a_\Gamma Y_\Gamma(\sigma)\quad(\sigma\in\Omega),\qquad\forall a\in\mathcal C^{\mathrm{good}}:\ \sum_{\Gamma:a\in U_\Gamma}|a_\Gamma|e^{\tau K_\Gamma}\le\rho\quad(4.18),$$
--   and $\sum_\Gamma\sup_{\sigma\in\Omega}|a_\Gamma Y_\Gamma(\sigma)|\le m\rho<\infty$, so the series converges absolutely and uniformly on $\Omega$. Here $\Gamma$ ranges over all ordered tuples of polymers (repetitions allowed) and $Z$, $a_\Gamma$, $U_\Gamma$, $K_\Gamma$, $Y_\Gamma$ are as in (4.13), (4.17). The expansion turns the core marginal into a finite-range interaction plus a summable remainder.
--
--   Differences from the source:
--   - reading: Under (4.8) → hypotheses Cond47 Φ and Cond48 Φ; reason: (4.7) is a standing assumption of §4 (p. 22) and the proof uses it (p. 24: |N_{H_Ψ}[γ]| ≤ D|γ|); (4.4) is the definition of ρ
--   - encoding: ln Z(σ) (presupposing Z(σ) > 0) → 0 < Z(σ) ∧ Real.log (Z σ) = …; reason: Real.log is the natural logarithm on positive reals; the positivity is part of the claim
--   - encoding: series over all tuples Γ → tsum over ClusterLabel (Poly Φ) with Summable clauses; reason: convergence and value are stated explicitly
--   - encoding: sup_{σ∈Ω} → real iSup over the finite subtype of Ω; reason: finite and bounded; for Ω = ∅ the value 0
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 24, Lemma 4.3

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure
import Definitions.Def_RandKSATSample_Main_PolymerModel
import Definitions.Def_RandKSATSample_Main_CoreChain

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Lemma 4.3: under (4.8) (with §4's standing (4.7)), for every `σ ∈ Ω`,
`ln Z(σ) = Σ_Γ a_Γ Y_Γ(σ)`; for every good clause `a`, `Σ_{Γ : a ∈ U_Γ} |a_Γ| e^{τ K_Γ} ≤ ρ`
(4.18); and `Σ_Γ sup_{σ ∈ Ω} |a_Γ Y_Γ(σ)| ≤ m ρ < ∞`, so the series converges absolutely and
uniformly on `Ω`. -/
theorem lemma_4_3 {n m k : ℕ} (Φ : Formula n m k) (h47 : Cond47 Φ) (h48 : Cond48 Φ) :
    (∀ σ ∈ Omega Φ, 0 < Zcore Φ σ ∧
      Summable (fun Γ : ClusterLabel (Poly Φ) => aGam Φ Γ * YGam Φ Γ σ) ∧
      Real.log (Zcore Φ σ) = ∑' Γ : ClusterLabel (Poly Φ), aGam Φ Γ * YGam Φ Γ σ) ∧
    (∀ a ∈ Cgood Φ,
      Summable (fun Γ : ClusterLabel (Poly Φ) =>
        if a ∈ UGam Φ Γ then |aGam Φ Γ| * Real.exp (tau n m k * KGam Φ Γ) else 0) ∧
      ∑' Γ : ClusterLabel (Poly Φ),
        (if a ∈ UGam Φ Γ then |aGam Φ Γ| * Real.exp (tau n m k * KGam Φ Γ) else 0) ≤
        rho n m k) ∧
    Summable (fun Γ : ClusterLabel (Poly Φ) =>
      ⨆ σ : {σ // σ ∈ Omega Φ}, |aGam Φ Γ * YGam Φ Γ σ.1|) ∧
    ∑' Γ : ClusterLabel (Poly Φ), (⨆ σ : {σ // σ ∈ Omega Φ}, |aGam Φ Γ * YGam Φ Γ σ.1|) ≤
      m * rho n m k := by sorry

end RandKSATSample.Main
