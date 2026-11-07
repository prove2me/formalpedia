-- Prove2me | Theorems.Thm_PathRecording_omega_reweightPlus
-- name    : PathRecording.omega_reweightPlus
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:44.94164+00:00
-- url     : https://prove2.me/theorems/bc33cab5-90c3-4732-8454-7c0b2aff0e77
-- title:
--   p.66 — $\Omega_{\mathcal A_t}$ and $W_t^+$ commute and $W_t^+W_t\Omega_{\mathcal A_t}=\Omega_{\mathcal A_t}$
-- statement:
--   For every choice of Schur–Weyl data for $\rho^{\otimes t}$,
--   $$\Omega_{\mathcal A_t}W_t^+=W_t^+\Omega_{\mathcal A_t}\qquad\text{and}\qquad W_t^+W_t\,\Omega_{\mathcal A_t}=\Omega_{\mathcal A_t}.$$
--
--   These two facts turn (5.21) into (5.22) in the proof of Theorem 5.3: on legal path states the reweighting $W_t$ applied by the previous query is undone by $W_t^+$.
--
--   Differences from the source:
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, p.66, the sentence after Eq. (5.22)

import Mathlib
import Definitions.Def_PathRecording_reweight

set_option autoImplicit false

namespace PathRecording

open Matrix

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, p.66, the step from (5.21) to (5.22): "`Ω_{𝒜_t}` and `W_t^+` commute and
`W_t^+ W_t Ω_{𝒜_t} = Ω_{𝒜_t}`". -/
theorem omega_reweightPlus {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}
    {ρ : UnitaryRep G N} {t : ℕ} (S : SchurWeylData ρ t) :
    S.omega * S.reweightPlus = S.reweightPlus * S.omega ∧
    S.reweightPlus * S.reweight * S.omega = S.omega := by sorry

end PathRecording
