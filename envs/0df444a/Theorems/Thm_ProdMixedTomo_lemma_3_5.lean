-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_3_5
-- name    : ProdMixedTomo.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:23.658719+00:00
-- url     : https://prove2.me/theorems/10a7125d-80e8-4f96-adee-c3cb913c008c
-- title:
--   Lemma 3.5 — dropping the off-diagonal of a qubit costs fidelity at most $2|a|^2$
-- statement:
--   Let $\rho=\begin{pmatrix}\sigma_1&a\\ \bar a&\sigma_2\end{pmatrix}$ be any one-qubit density matrix and $\rho_{\mathrm{diag}}=\begin{pmatrix}\sigma_1&0\\0&\sigma_2\end{pmatrix}$ its diagonal part. Then
--   $$
--   F(\rho,\rho_{\mathrm{diag}})\ \ge\ 1-2|a|^2,
--   $$
--   where $F$ is the squared fidelity. Through the multiplicativity of fidelity and the Fuchs–van de Graaf inequality, this controls the trace-distance cost of ignoring the off-diagonal terms in the learned eigenbasis.
--
--   Differences from the source:
--   - encoding: the 2×2 matrix with rows (σ₁, a), (ā, σ₂) → Matrix Bool Bool ℂ, a = ρ false true, σ₁, σ₂ the diagonal entries; reason: index convention only
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 3.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_Fidelity

open scoped ComplexOrder

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 3.5, p.17 (PDF p.19). For a one-qubit density matrix `ρ = [[σ₁, a], [ā, σ₂]]` with
diagonal part `ρ_diag = diag(σ₁, σ₂)`, the (squared) fidelity satisfies
`F(ρ, ρ_diag) ≥ 1 − 2|a|²`.

**Formalization Note.** `a = ρ₀₁` is the (complex) off-diagonal entry, `ā = ρ₁₀`; `|a|` is its
modulus; the one-qubit basis is indexed by `Bool` (`false` ↔ the first row). -/
theorem lemma_3_5 (ρ : Matrix Bool Bool ℂ) (hρ : IsDensity ρ) :
    1 - 2 * ‖ρ false true‖ ^ 2 ≤ fidelity ρ (Matrix.diagonal fun i => ρ i i) := by sorry

end ProdMixedTomo
