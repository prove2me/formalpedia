-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_5_11
-- name    : ShadowBootstrap.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:55.721806+00:00
-- url     : https://prove2.me/theorems/bdcd33fc-5458-4095-ae3a-faca2e0d7388
-- title:
--   Lemma 5.11 — error propagation at a node: children's error plus $2\|\hat B_x - B_x\|_{op}$
-- statement:
--   Let $\varphi$ be the (unnormalized) conditional vector $\varphi_x = \sqrt{p_x}\,|\psi_x\rangle$ of a node $x$ on $D+1$ suffix qubits, $p_x = \|\varphi\|_2^2$, and $\varphi_{xc}(y) = \varphi(c, y)$ its children's vectors. Let $|\hat\psi_{x0}\rangle, |\hat\psi_{x1}\rangle$ be unit child estimates, $|q_c\rangle = |c\rangle\otimes|\hat\psi_{xc}\rangle$, $B_x$ the matrix of Definition 5.5, $\hat B_x$ any Hermitian $2\times2$ matrix, and $\hat\alpha$ any normalized eigenvector of $\hat B_x$ for its largest eigenvalue. Then $|\hat\psi_x\rangle := \hat\alpha_0|q_0\rangle + \hat\alpha_1|q_1\rangle$ satisfies
--   $$p_x\big(1 - |\langle\psi_x|\hat\psi_x\rangle|^2\big) \le p_{x0}\big(1 - |\langle\psi_{x0}|\hat\psi_{x0}\rangle|^2\big) + p_{x1}\big(1 - |\langle\psi_{x1}|\hat\psi_{x1}\rangle|^2\big) + 2\|\hat B_x - B_x\|_{op},$$
--   where $p(1 - |\langle\psi_\cdot|v\rangle|^2)$ is written $\|\varphi\|_2^2 - |\langle\varphi|v\rangle|^2$.
--
--   The first two terms are the error inherited from the child nodes, the last the error at the current node.
--
--   Differences from the source:
--   - generalization: φ_x = √p_x|ψ_x⟩ for a unit state ψ → any vector φ on the suffix; reason: the argument uses no property of φ; the paper's φ_x is a special case
--   - encoding: p_x(1 − |⟨ψ_x|v⟩|²) → ‖φ_x‖² − |⟨φ_x|v⟩|²; reason: equal when p_x > 0 and defined when p_x = 0
--   - reading: α̂ a normalized eigenvector for the largest eigenvalue (any vector of the eigenspace if repeated) → every unit α̂ maximizing v†B̂_xv over unit v; reason: for a Hermitian matrix these are the same vectors
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 5.11 and its proof, pp.20–21, with Definition 5.5 and Eq. (22)

import Mathlib
import Definitions.Def_ShadowBootstrap_recon

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 5.11, p.20 (error propagation at a node): for every node `x`, normalized child estimates
`|ψ̂_{x0}⟩, |ψ̂_{x1}⟩` and Hermitian estimate `B̂_x`, the reconstruction `|ψ̂_x⟩ = |q_α̂⟩` of Eq. (22)
satisfies
`p_x(1 − |⟨ψ_x|ψ̂_x⟩|²) ≤ p_{x0}(1 − |⟨ψ_{x0}|ψ̂_{x0}⟩|²) + p_{x1}(1 − |⟨ψ_{x1}|ψ̂_{x1}⟩|²) + 2‖B̂_x − B_x‖_op`.

**Formalization Note** The node's unnormalized conditional vector `φ_x = (⟨x| ⊗ I)|ψ⟩` is any
vector `φ` on `{0,1}^{D+1}` (`D + 1 = n − ℓ` suffix qubits); `p_x = ‖φ‖₂²` and
`p_x(1 − |⟨ψ_x|v⟩|²) = ‖φ‖₂² − |⟨φ|v⟩|²`, which is also meaningful at `p_x = 0`. The children's
conditional vectors are `φ_{xc}(y) = φ(c, y)`. `B_x` is Definition 5.5 (`Bmat`), `u c` the child
estimates, and `α̂` **any** normalized eigenvector of `B̂_x` for its largest eigenvalue
(`IsTopEigvec`: a unit vector maximizing `v†B̂_xv`). -/
theorem lemma_5_11 (D : ℕ) (φ : Bits (D + 1) → ℂ) (u : Fin 2 → Bits D → ℂ)
    (hu : ∀ c, IsUnitVec (u c)) (Bh : Matrix (Fin 2) (Fin 2) ℂ) (hBh : Bh.IsHermitian)
    (α : Fin 2 → ℂ) (hα : IsTopEigvec Bh α) :
    vnormSq φ - ‖braket φ (combine u α)‖ ^ 2 ≤
      ∑ c : Fin 2, (vnormSq (fun y : Bits D => φ (Fin.cons c y)) -
          ‖braket (fun y : Bits D => φ (Fin.cons c y)) (u c)‖ ^ 2)
        + 2 * opNorm (Bh - Bmat φ u) := by sorry

end ShadowBootstrap
