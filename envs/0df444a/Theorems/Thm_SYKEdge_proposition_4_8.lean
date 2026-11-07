-- Prove2me | Theorems.Thm_SYKEdge_proposition_4_8
-- name    : SYKEdge.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:32.226934+00:00
-- url     : https://prove2.me/theorems/9b6c8e2c-42b2-434b-ab25-dad9e8ab3d7f
-- title:
--   Proposition 4.8 — $(q-\delta)uu^*-(\rho^-+\delta)\Pi_{u^\perp}\preceq\mathcal E\preceq(q+\delta)uu^*+(\rho^++\delta)\Pi_{u^\perp}$
-- statement:
--   Let $\mathcal E$ be the sign matrix of a $k$-uniform hypergraph $\mathcal H$, $u$ the uniform unit vector, $\Pi_{u^\perp}=\mathrm{Id}-uu^*$, and $q,\delta,\rho^\pm$ the leakage parameters (13)–(19). Then, in the Loewner order,
--   $$(q-\delta)\,uu^*-(\rho^-+\delta)\,\Pi_{u^\perp}\ \preceq\ \mathcal E\ \preceq\ (q+\delta)\,uu^*+(\rho^++\delta)\,\Pi_{u^\perp}.$$
--
--   The two-sided sandwich reduces the sign matrix to the uniform channel plus a transverse error, which is how $q,\delta,\rho^\pm$ enter every later bound.
--
--   **Formalization Note** $A\preceq B$ is "$B-A$ is positive semidefinite" for complex $|\mathcal H|\times|\mathcal H|$ matrices.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Proposition 4.8, p.26

import Mathlib
import Definitions.Def_SYKEdge_SignMatrix
import Definitions.Def_SYKEdge_Hamiltonian
open Matrix ComplexOrder

namespace SYKEdge

/-- **Proposition 4.8**, A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.26.

`(q − δ)uu* − (ρ⁻ + δ)Π_{u⊥} ≼ ℰ ≼ (q + δ)uu* + (ρ⁺ + δ)Π_{u⊥}`.

**Formalization Note.** `≼` is the Loewner order on `ℂ^{H×H}` (the difference is positive
semidefinite). `ℰ, u, Π_{u⊥}, q, δ, ρ±` are (13)–(19) for the hypergraph `H = (S₁, …, S_m)` under the
§3 standing assumptions. -/
theorem proposition_4_8 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S) :
    (signMat S - ((((qParam S - deltaParam S : ℝ)) : ℂ) • uuStar (Fin m) -
        (((rhoMinus S + deltaParam S : ℝ)) : ℂ) • projPerp (Fin m))).PosSemidef ∧
    ((((qParam S + deltaParam S : ℝ)) : ℂ) • uuStar (Fin m) +
        (((rhoPlus S + deltaParam S : ℝ)) : ℂ) • projPerp (Fin m) - signMat S).PosSemidef := by sorry

end SYKEdge
