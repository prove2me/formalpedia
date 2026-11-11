-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_3_4
-- name    : ProdMixedTomo.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:23.228965+00:00
-- url     : https://prove2.me/theorems/2eaf1db4-9c36-48d5-b8e5-18235bfb38b7
-- title:
--   Lemma 3.4 — measuring with any POVM cannot increase distance: $d_{\mathrm{tv}}(p,q)\le d_{\mathrm{tr}}(\rho,\sigma)$
-- statement:
--   Let $\rho,\sigma$ be density matrices on a finite-dimensional Hilbert space and let $\{M_i\}_{i\in\iota}$ be a POVM: $M_i\succeq0$ and $\sum_iM_i=I$. Let $p(i)=\operatorname{tr}(\rho M_i)$ and $q(i)=\operatorname{tr}(\sigma M_i)$ be the outcome distributions. Then
--   $$
--   d_{\mathrm{tv}}(p,q)=\frac12\sum_{i}|p(i)-q(i)|\ \le\ d_{\mathrm{tr}}(\rho,\sigma).
--   $$
--   In the reduction this turns closeness of $\rho$ to a product state into $\epsilon$-contamination of the classical outcomes of any single-qubit measurement.
--
--   **Formalization Note** The outcome family $\iota$ is arbitrary and $\sum_iM_i=I$ is an unconditional sum (`HasSum`); $p,q$ are the real parts of the traces (which are real).
--
--   Differences from the source:
--   - generalization: ρ, σ ∈ ℂ^{2ⁿ×2ⁿ}, a POVM M → density matrices on any finite index type κ, a POVM with any outcome family ι (Σ Mᵢ = I as HasSum); reason: κ = {0,1}ⁿ and a finite outcome set are special cases (a finite family has the finite sum as its HasSum)
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 3.4, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance

open scoped ComplexOrder

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 3.4, p.16 (PDF p.18). Measuring two density matrices `ρ, σ` with the same POVM `{Mᵢ}`
gives outcome distributions `p(i) = Re tr(ρ Mᵢ)`, `q(i) = Re tr(σ Mᵢ)` with
`d_tv(p, q) = ½ Σᵢ |p(i) − q(i)| ≤ d_tr(ρ, σ)`.

**Formalization Note.** Generalization: the Hilbert-space index is any finite type `κ` (the
paper's `ℂ^{2ⁿ×2ⁿ}` is `κ = Fin n → Bool`) and the POVM has any family of outcomes `ι` with
`Σᵢ Mᵢ = I` as an unconditional sum (finite POVMs are the case `ι` finite). -/
theorem lemma_3_4 {κ ι : Type*} [Fintype κ] [DecidableEq κ] (ρ σ : Matrix κ κ ℂ)
    (M : ι → Matrix κ κ ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hM : ∀ i, (M i).PosSemidef) (hsum : HasSum M 1) :
    (∑' i, |(ρ * M i).trace.re - (σ * M i).trace.re|) / 2 ≤ dtr ρ σ := by sorry

end ProdMixedTomo
