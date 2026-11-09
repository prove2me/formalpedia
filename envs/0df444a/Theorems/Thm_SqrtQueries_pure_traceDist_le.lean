-- Prove2me | Theorems.Thm_SqrtQueries_pure_traceDist_le
-- name    : SqrtQueries.pure_traceDist_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:28:55.617941+00:00
-- url     : https://prove2.me/theorems/9030a37d-ac50-4782-b3a8-98e1d702459f
-- title:
--   Proof of Theorem 3.3 — trace distance of pure states at most their $L^2$ distance
-- statement:
--   Let $\psi,\varphi\in\mathbb C^n$ be unit vectors. Then
--   $$
--   D\big(|\psi\rangle\langle\psi|,\,|\varphi\rangle\langle\varphi|\big)=\tfrac12\big\||\psi\rangle\langle\psi|-|\varphi\rangle\langle\varphi|\big\|_1\le\|\psi-\varphi\| .
--   $$
--
--   In the proof of Theorem 3.3 this is the step "this immediately implies the same bound for trace distance": the $L^2$ bound on the end states transfers to their trace distance.
--
--   **Formalization Note** $|\psi\rangle\langle\psi|$ is the matrix with entries $\psi_i\overline{\psi_j}$, and the trace distance is half of `WildeQIT.traceDist`.
--
--   Differences from the source:
--   - reading: this immediately implies the same bound for trace distance → D(|ψ⟩⟨ψ|, |φ⟩⟨φ|) ≤ ‖ψ − φ‖ for unit vectors ψ, φ; reason: this is the general inequality the sentence applies to the two end states
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), proof of Theorem 3.3, p.18

import Mathlib
import Definitions.Def_WildeQIT_traceDist

namespace SqrtQueries

/-- **Pure-state trace distance** in the proof of Theorem 3.3 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.18: the `L2` bound on the
end states "immediately implies the same bound for trace distance". For unit vectors `ψ`, `φ`,
`D(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = ½‖|ψ⟩⟨ψ| − |φ⟩⟨φ|‖₁ ≤ ‖ψ − φ‖`.

**Formalization Note.** `|ψ⟩⟨ψ|` is `Matrix.vecMulVec ψ (star ψ)` (entries `ψ_i \overline{ψ_j}`),
the norm on vectors is the Euclidean norm, and the paper's trace distance is
`(1/2) * WildeQIT.traceDist` (the published `traceDist` has no factor `½`). -/
theorem pure_traceDist_le {n : Type} [Fintype n] [DecidableEq n] (ψ φ : EuclideanSpace ℂ n)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    (1 / 2) * WildeQIT.traceDist (Matrix.vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ‖ψ - φ‖ := by sorry

end SqrtQueries
