-- Prove2me | Theorems.Thm_PathRecording_reweight_identities
-- name    : PathRecording.reweight_identities
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:18.852875+00:00
-- url     : https://prove2.me/theorems/fc3927b9-a9a4-4d24-b357-807c06154f5f
-- title:
--   p.62 — $W_t^+W_t=W_tW_t^+=\Pi_{\mathrm{diag},t}$ and $\Omega_{\mathcal A_t}\preceq\Pi_{\mathrm{diag},t}$
-- statement:
--   For every choice of Schur–Weyl data for $\rho^{\otimes t}$, the reweighting operators $W_t$ (5.6) and $W_t^+$ (5.7) satisfy
--   $$W_t^+W_t=W_tW_t^+=\Pi_{\mathrm{diag},t},$$
--   and the commutant EPR projector is dominated by the equal-label projector in the Loewner order:
--   $$\Omega_{\mathcal A_t}\preceq\Pi_{\mathrm{diag},t}.$$
--
--   So $W_t^+$ is an inverse of $W_t$ on the legal path subspace, which is what the path-recording update (5.8) uses.
--
--   Differences from the source:
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
--   - encoding: Ω_{𝒜_t} ⪯ Π_{diag,t} → Π_{diag,t} − Ω_{𝒜_t} is positive semidefinite; reason: definition of the Loewner order
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, p.62, the two displays after Eq. (5.7)

import Mathlib
import Definitions.Def_PathRecording_reweight

set_option autoImplicit false

namespace PathRecording

open Matrix
open scoped ComplexOrder

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, p.62 (after Eq. (5.7)): for every Schur–Weyl data of `ρ^{⊗t}`,
`W_t^+ W_t = W_t W_t^+ = Π_{diag,t}` and `Ω_{𝒜_t} ⪯ Π_{diag,t}` (Loewner order:
`Π_{diag,t} − Ω_{𝒜_t}` is positive semidefinite). -/
theorem reweight_identities {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}
    {ρ : UnitaryRep G N} {t : ℕ} (S : SchurWeylData ρ t) :
    S.reweightPlus * S.reweight = S.projDiag ∧
    S.reweight * S.reweightPlus = S.projDiag ∧
    (S.projDiag - S.omega).PosSemidef := by sorry

end PathRecording
