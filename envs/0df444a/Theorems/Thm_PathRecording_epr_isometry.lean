-- Prove2me | Theorems.Thm_PathRecording_epr_isometry
-- name    : PathRecording.epr_isometry
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:08:22.276201+00:00
-- url     : https://prove2.me/theorems/e0395186-d55b-4474-947c-fe676675bd08
-- title:
--   p.64 — $E_t^\dagger E_t=\Pi_{\mathrm{Tab}_t}$ and $E_tE_t^\dagger=\widehat\Pi^{\mathcal A_t}_{\mathrm{EPR},t}$
-- statement:
--   For every choice of Schur–Weyl data for $\rho^{\otimes t}$, the $\mathcal A_t$ EPR isometry $E_t$ satisfies
--   $$E_t^\dagger E_t=\Pi_{\mathrm{Tab}_t},\qquad E_tE_t^\dagger=\widehat\Pi^{\mathcal A_t}_{\mathrm{EPR},t}.$$
--
--   These identities give Claim 5.4: $\Gamma_t=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)E_t$ is an isometry from $\mathrm{Tab}_t$ onto the image of $\Omega_{\mathcal A_t}$.
--
--   Differences from the source:
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: E_t on ⨁_{λ∈Ĝ} V^λ_G ⊗ \overline{V^λ_G} and Π_{Tab_t} the projector onto Tab_t → E_t on Tab_t and the identity of Tab_t; reason: E_t vanishes off Tab_t, so the identities restrict to Tab_t without change
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, p.64, display after the adjoint of E_t

import Mathlib
import Definitions.Def_PathRecording_Gamma

set_option autoImplicit false

namespace PathRecording

open Matrix

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, p.64: "it follows directly that `E_t† E_t = Π_{Tab_t}`,
`E_t E_t† = Π̂^{𝒜_t}_{EPR,t}`".

**Formalization Note.** `E_t` is defined on `Tab_t` itself, so `Π_{Tab_t}` is the identity of
`Tab_t`. -/
theorem epr_isometry {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}
    {ρ : UnitaryRep G N} {t : ℕ} (S : SchurWeylData ρ t) :
    S.eprIsometryᴴ * S.eprIsometry = 1 ∧
    S.eprIsometry * S.eprIsometryᴴ = S.eprProjHat := by sorry

end PathRecording
