-- Prove2me | Theorems.Thm_RennerKoenig_lemma_4_4
-- name    : RennerKoenig.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:16.288922+00:00
-- url     : https://prove2.me/theorems/250d1022-9983-49e6-b079-2ab869a78be0
-- title:
--   Lemma 4.4 — $\delta(\rho,\sigma)\le\frac12\sqrt{\operatorname{rank}(\rho-\sigma)\,\Delta(\rho,\sigma)}$
-- statement:
--   Let $\rho$ and $\sigma$ be density operators on a Hilbert space. Then
--
--   $$
--   \delta(\rho,\sigma)\le\frac12\sqrt{\operatorname{rank}(\rho-\sigma)\cdot\Delta(\rho,\sigma)}.
--   $$
--
--   The trace distance is thus controlled by the Hilbert–Schmidt distance, which can be computed directly.
--
--   Differences from the source:
--   - encoding: rank(ρ − σ), possibly infinite → hypothesis that the range of ρ − σ is finite-dimensional; reason: it excludes only rank(ρ − σ) = ∞, where the printed right side is +∞
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 4.4, p.9

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_traceDist
import Definitions.Def_RennerKoenig_hsDistSq
import Definitions.Def_RennerKoenig_rankOp

namespace RennerKoenig

/-- **Lemma 4.4.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 4.4, p.9: for density operators `ρ, σ` on `H`,
`δ(ρ, σ) ≤ ½ √(rank(ρ − σ) · Δ(ρ, σ))`.

**Formalization Note** `hfin` excludes only `rank(ρ − σ) = ∞`, where the printed right side is
`+∞`. -/
theorem lemma_4_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ σ : H →L[ℂ] H)
    (hρ : ScutaruFid.IsDensityOperator (chosenBasis H) ρ)
    (hσ : ScutaruFid.IsDensityOperator (chosenBasis H) σ)
    (hfin : FiniteDimensional ℂ (LinearMap.range ((ρ - σ : H →L[ℂ] H) : H →ₗ[ℂ] H))) :
    traceDist ρ σ ≤
      (1 / 2 : ℝ) * Real.sqrt ((rankOp (ρ - σ) : ℝ) * hsDistSq ρ σ) := by sorry

end RennerKoenig
