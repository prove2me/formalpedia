-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_3_2
-- name    : UnitaryQIPPSPACE.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:06.929745+00:00
-- url     : https://prove2.me/theorems/4b4b90aa-8588-4fb4-b441-cf9825c6899d
-- title:
--   Lemma 3.2 — soundness limits acceptance variation
-- statement:
--   Let $s,\delta\in[0,1]$, let $\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H)$ be a completely positive trace-non-increasing linear map and $U$ a unitary on $\mathcal H$. Suppose that for every pure state $|\psi\rangle$,
--   $$\operatorname{tr}[\Phi(\psi)]>s\implies\mathrm{TD}\Big(\frac{\Phi(\psi)}{\operatorname{tr}[\Phi(\psi)]},U\psi U^\dagger\Big)\le\delta.$$
--   Let $\lambda_{\max},\lambda_{\min}$ be the largest and smallest eigenvalues of $\Phi^*(I_{\mathcal H})$. Then for every $t\in(0,1)$ with $t\lambda_{\max}>s$,
--   $$\lambda_{\max}-\lambda_{\min}\le\frac{\delta(1+t)}{t(1-t)}\lambda_{\max}.$$
--
--   Applied to the accepting branch of a protocol with a fixed prover, it says that soundness forces the acceptance probability to be nearly the same on every input.
--
--   Differences from the source:
--   - encoding: a Hilbert space H → H = ℂ^ι for a finite index type ι; reason: the paper's H is finite dimensional
--   - encoding: eigenvalues λ_max, λ_min of Φ*(I) → the maximum and minimum of ⟨v|Φ*(I)|v⟩ over unit vectors v; reason: equal for the Hermitian Φ*(I)
--   - encoding: completely positive → Choi matrix positive semidefinite; reason: Choi's theorem
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 3.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_IsCP
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_UnitaryQIPPSPACE_conjBy
import Definitions.Def_UnitaryQIPPSPACE_hsAdjoint

open Matrix

namespace UnitaryQIPPSPACE

/-- **Lemma 3.2** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version sha256
9e357a00…, p. 14 (PDF p. 16)): "Let `s, δ ∈ [0, 1]`, `Φ : L(H) → L(H)` be a completely positive and
trace-nonincreasing linear map, and `U` be a unitary on `H`. Suppose that, for every pure state `|ψ⟩`
in `H`, `tr[Φ(ψ)] > s ⟹ TD(Φ(ψ)/tr[Φ(ψ)], UψU†) ≤ δ`. (2) Denote by `λ_max` and `λ_min` the largest
and smallest eigenvalues of `Φ*(I_H)`, respectively. Then, for every `t ∈ (0, 1)` satisfying
`t · λ_max > s`, it holds that `λ_max − λ_min ≤ δ(1 + t)/(t(1 − t)) · λ_max`."

**Formalization Note** `H = ℂ^ι` for any finite index type `ι`. `Φ*` is the Hilbert–Schmidt adjoint,
and `λ_max`, `λ_min` of the Hermitian matrix `Φ*(I)` are the extremes of its Rayleigh quotient over
unit vectors, which are its largest and smallest eigenvalues. -/
theorem lemma_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] (s δ : ℝ) (hs : 0 ≤ s ∧ s ≤ 1)
    (hδ : 0 ≤ δ ∧ δ ≤ 1) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hCP : IsCP Φ) (hTNI : IsTNI Φ)
    (U : Matrix.unitaryGroup ι ℂ)
    (h2 : ∀ ψ : ι → ℂ, ShadowBootstrap.IsUnitVec ψ → s < (Φ (ObliviousRSP.pureState ψ)).trace.re →
      DimFreeShadow.traceDistance ((((Φ (ObliviousRSP.pureState ψ)).trace.re : ℝ) : ℂ)⁻¹ • Φ (ObliviousRSP.pureState ψ))
        (conjBy (U : Matrix ι ι ℂ) (ObliviousRSP.pureState ψ)) ≤ δ)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (hts : s < t * SYKEdge.lamMax (hsAdjoint Φ 1)) :
    SYKEdge.lamMax (hsAdjoint Φ 1) - SYKEdge.lamMin (hsAdjoint Φ 1)
      ≤ δ * (1 + t) / (t * (1 - t)) * SYKEdge.lamMax (hsAdjoint Φ 1) := by sorry

end UnitaryQIPPSPACE
