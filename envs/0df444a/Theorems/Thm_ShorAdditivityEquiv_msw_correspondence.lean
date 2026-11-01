-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_msw_correspondence
-- name    : ShorAdditivityEquiv.msw_correspondence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:06.056735+00:00
-- url     : https://prove2.me/theorems/1189a05f-9bf4-4b7d-9f0b-c7f3f9a744c1
-- title:
--   §3, p. 7 — the MSW correspondence $\chi_N(\rho)=H(N(\rho))-E_F(V\rho V^\dagger)$
-- statement:
--   Let $V:\mathcal H_{\mathrm{in}}\to\mathcal H_A\otimes\mathcal H_B$ be an isometry ($V^\dagger V=I$), let $N$ be the channel $N(\mu)=\mathrm{Tr}_B(V\mu V^\dagger)$, and let $\rho$ be a density matrix on $\mathcal H_{\mathrm{in}}$ with $\sigma=V\rho V^\dagger$. Then
--   $$
--   \chi_N(\rho) = H\big(N(\rho)\big) - E_F(\sigma),
--   $$
--   where $\chi_N(\rho)$ is the constrained Holevo capacity (Eq. (3)) and $E_F$ the entanglement of formation across $A\,|\,B$ (Eq. (2)). This is the correspondence of Matsumoto, Shimono and Winter: an ensemble $\{p_i,|\phi_i\rangle\}$ of $\rho$ is mapped to the ensemble $\{p_i,V|\phi_i\rangle\}$ of $\sigma$, and $N(|\phi_i\rangle\langle\phi_i|)=\mathrm{Tr}_B|v_i\rangle\langle v_i|$.
--
--   It translates statements about the entanglement of formation into statements about channel capacities and back, and is used in every implication of Theorem 1 that passes between (i)/(ii) and (iii)/(iv).
--
--   Differences from the source:
--   - encoding: a channel N with a unitary embedding U(ρ) = VρV† such that N(µ) = TrB U(µ) (Stinespring) → an arbitrary isometry V : Matrix (A × B) I ℂ with Vᴴ * V = 1 and the map μ ↦ traceRight (V μ Vᴴ); reason: every channel has such a dilation (p.2) and every such map is a channel; the identity is about the pair (N, V)
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §3, pp. 6–7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_ShorAdditivityEquiv_constrainedHolevo

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08
open scoped Matrix

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §3, pp.6–7, unnumbered (the Matsumoto–Shimono–Winter correspondence): for a channel
`N(µ) = Tr_B U(µ)` given by a unitary embedding `U(ρ) = VρV†` of `H_in` into `H_A ⊗ H_B`,
and `σ = U(ρ)`, "Since N(|φi⟩⟨φi|) = TrB|vi⟩⟨vi|, we have χN(ρ) = H(N(ρ)) − EF(σ)."

**Formalization Note.** The unitary embedding is a matrix `V : (A × B) × I` with `V†V = 1`
(an isometry onto its range, as on p.2), and `N μ = Tr_B (V μ V†)` with `Tr_B` =
`QAlgorithms.traceRight` (traces the second factor). `ρ` is any density matrix on `H_in`.
`χ_N(ρ)` is `constrainedHolevo` (Eq. (3)) and `E_F` is the published `formation` (Eq. (2)),
both on pure-state ensembles. -/
theorem msw_correspondence {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] (V : Matrix (A × B) I ℂ) (hV : Vᴴ * V = 1)
    (ρ : Matrix I I ℂ) (hρ : IsDensityMatrix ρ) :
    constrainedHolevo (fun μ => traceRight (V * μ * Vᴴ)) ρ =
      vnEntropy (traceRight (V * ρ * Vᴴ)) - formation (V * ρ * Vᴴ) := by sorry

end ShorAdditivityEquiv
