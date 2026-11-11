-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_1
-- name    : UnitaryQIPPSPACE.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:27.610284+00:00
-- url     : https://prove2.me/theorems/f19616be-5658-4438-b65d-162e9de3399c
-- title:
--   Lemma 4.1 — recovering the exact unitary
-- statement:
--   Let $C$ be a quantum channel and $U$ a unitary on $\mathcal H$ with $\mathrm{TD}(C(\psi),U\psi U^\dagger)\le\gamma$ for every unit $|\psi\rangle$, where $0\le\gamma\le2^{-10}$. Fix a unit vector $|\phi\rangle$ and set $\sigma:=C(|\phi\rangle\langle\phi|)$. Then:
--   1. $\lambda_{\max}(\sigma)$ has multiplicity $1$ and $\lambda_{\max}(\sigma)\ge1-\gamma$.
--   2. For every unit eigenvector $|v_{\max}\rangle$ of $\sigma$ for $\lambda_{\max}(\sigma)$, the operator $B$ of eq. (12) ($B|\phi\rangle=|v_{\max}\rangle$, $B|\phi^\perp\rangle=Q_{v_{\max}}C(|\phi^\perp\rangle\langle\phi|)|v_{\max}\rangle$) satisfies $\|B-zU\|_{\mathrm{op}}\le8\sqrt\gamma$ for some $|z|=1$.
--   3. The singular values of $B$ lie in $[1-8\sqrt\gamma,1+8\sqrt\gamma]\subseteq[3/4,5/4]$, and $W:=B(B^\dagger B)^{-1/2}$ satisfies $\|W-zU\|_{\mathrm{op}}\le16\sqrt\gamma$ with the same $z$.
--
--   An approximately unitary channel thus determines an exact unitary at square-root cost.
--
--   Differences from the source:
--   - reading: "Let |v_max⟩ be the eigenstate of σ for λ_max(σ)" (a phase is not fixed) → clauses 2–3 for every unit eigenvector, one z for both bounds; reason: the strongest reading; B and W scale with the phase of v_max and z absorbs it
--   - encoding: the singular values of B lie in [a, b] → a‖x‖ ≤ ‖Bx‖ ≤ b‖x‖ for every x; reason: equivalent for a ≥ 0
--   - encoding: multiplicity of λ_max(σ) → dimension of the eigenspace; reason: σ is Hermitian, so geometric and algebraic multiplicities agree
--   - encoding: a Hilbert space H; λ_max; complete positivity → ℂ^ι; Rayleigh-quotient maximum; Choi matrix positive semidefinite; reason: standard equivalent forms
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_IsCP
import Definitions.Def_UnitaryQIPPSPACE_roundB
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix

namespace UnitaryQIPPSPACE

/-- **Lemma 4.1 (Recovering the exact unitary)** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, pp. 18–19 (PDF pp. 20–21)): "Let `C` be a quantum
channel and `U` a unitary, both acting on `H`, such that `TD(C(ψ), U(ψ)) ≤ γ` for every `|ψ⟩ ∈ H`, and
assume that `0 ≤ γ ≤ 2^{−10}`. Fix `|ϕ⟩ ∈ H` and set `σ := C(|ϕ⟩⟨ϕ|)`, then
1. The largest eigenvalue `λ_max(σ)` has multiplicity 1, and satisfies `λ_max(σ) ≥ 1 − γ`.
2. Let `|v_max⟩` be the eigenstate of `σ` for `λ_max(σ)`, and `Q_{v_max} = I − |v_max⟩⟨v_max|`.
Define a linear operator `B ∈ L(H)` via the following actions: `B|ϕ⟩ = |v_max⟩`,
`∀ |ϕ^⊥⟩ : ⟨ϕ|ϕ^⊥⟩ = 0, B|ϕ^⊥⟩ = Q_{v_max} C(|ϕ^⊥⟩⟨ϕ|) |v_max⟩`. (12) Then there exists a complex
number `z ∈ ℂ` with `|z| = 1` such that `‖B − zU‖_op ≤ 8√γ`.
3. The singular values of `B` lie in the interval `[1 − 8√γ, 1 + 8√γ] ⊆ [3/4, 5/4]`, and the unitary
projection `W := B(B†B)^{−1/2}` satisfies `‖W − zU‖_op ≤ 16√γ`."

Clauses 2–3 are stated for every unit eigenvector `v_max` of `σ` for `λ_max(σ)`, with one `z` for
both bounds. "The singular values of `B` lie in `[a, b]`" (`a ≥ 0`) is stated as
`a‖x‖ ≤ ‖Bx‖ ≤ b‖x‖` for every vector `x`.

**Formalization Note** `H = ℂ^ι`; a quantum channel is a completely positive trace-preserving
linear map; `|ϕ⟩` and the `|ψ⟩` of the hypothesis are unit vectors. The multiplicity of `λ_max(σ)` is
the dimension of its eigenspace (σ is Hermitian). `λ_max(σ)` is the maximum of the Rayleigh quotient
of `σ`. -/
theorem lemma_4_1 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hCP : IsCP C) (hTP : IsTP C) (U : Matrix.unitaryGroup ι ℂ) (γ : ℝ)
    (hTD : ∀ ψ : ι → ℂ, ShadowBootstrap.IsUnitVec ψ →
      DimFreeShadow.traceDistance (C (ObliviousRSP.pureState ψ)) (conjBy (U : Matrix ι ι ℂ) (ObliviousRSP.pureState ψ)) ≤ γ)
    (hγ : 0 ≤ γ ∧ γ ≤ (1 / 2 : ℝ) ^ 10) (ϕ : ι → ℂ) (hϕ : ShadowBootstrap.IsUnitVec ϕ) :
    (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (C (ObliviousRSP.pureState ϕ)))
        ((SYKEdge.lamMax (C (ObliviousRSP.pureState ϕ)) : ℝ) : ℂ)) = 1 ∧
      1 - γ ≤ SYKEdge.lamMax (C (ObliviousRSP.pureState ϕ))) ∧
    ∀ v : ι → ℂ, ShadowBootstrap.IsUnitVec v →
      (C (ObliviousRSP.pureState ϕ)).mulVec v = ((SYKEdge.lamMax (C (ObliviousRSP.pureState ϕ)) : ℝ) : ℂ) • v →
      ∃ z : ℂ, ‖z‖ = 1 ∧
        AgnosticTNS.opNorm (roundB C ϕ v - z • (U : Matrix ι ι ℂ)) ≤ 8 * Real.sqrt γ ∧
        (∀ x : ι → ℂ, (1 - 8 * Real.sqrt γ) * SYKEdge.vecNorm x ≤ SYKEdge.vecNorm ((roundB C ϕ v).mulVec x) ∧
          SYKEdge.vecNorm ((roundB C ϕ v).mulVec x) ≤ (1 + 8 * Real.sqrt γ) * SYKEdge.vecNorm x) ∧
        3 / 4 ≤ 1 - 8 * Real.sqrt γ ∧ 1 + 8 * Real.sqrt γ ≤ 5 / 4 ∧
        AgnosticTNS.opNorm (roundW (roundB C ϕ v) - z • (U : Matrix ι ι ℂ)) ≤ 16 * Real.sqrt γ := by sorry

end UnitaryQIPPSPACE
