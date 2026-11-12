-- Prove2me | Theorems.Thm_QubitTracking_fact_4_5
-- name    : QubitTracking.fact_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:29:29.307813+00:00
-- url     : https://prove2.me/theorems/cc4bc867-93c9-43c4-bb2d-d35f7f7de6a7
-- title:
--   Fact 4.5 — the anchor state lives on $T+v$ (standard basis) and $S^\perp+u$ (Hadamard basis) and is symmetric under $H$
-- statement:
--   Let $d=n_h+n_e+n_s$ and $(\mathsf{sk},|\Psi^{\mathsf{sk}}_{n_e,n_h,n_s}\rangle)\leftarrow\mathsf{GenAnchorState}_{n_e,n_h,n_s}(1^\lambda)$. Then:
--
--   1. the standard-basis measurement of the vessel always outputs a vector in $T+v$;
--   2. the Hadamard-basis measurement of the vessel always outputs a vector in $S^\perp+u$;
--   3. the two distributions
--   $$\{S,T,u,v,|\Psi^{\mathsf{sk}}_{n_e,n_h,n_s}\rangle\}\quad\text{and}\quad\{T^\perp,S^\perp,v,u,(H^{\otimes n_e}_{\mathbf A}\otimes H^{\otimes d}_{\mathbf B})|\Psi^{\mathsf{sk}}_{n_e,n_s,n_h}\rangle\},$$
--   the first with $\mathsf{sk}\leftarrow\mathsf{GenAnchorState}_{n_e,n_h,n_s}$ and the second with $\mathsf{sk}\leftarrow\mathsf{GenAnchorState}_{n_e,n_s,n_h}$, are equal.
--
--   Clauses 1–2 are why the honest prover's coherent queries never disturb the vessel (completeness of Theorem 9.6); clause 3 transfers results about the standard basis to the Hadamard basis (Corollary 7.5).
--
--   Differences from the source:
--   - encoding: n_e, n_h, n_s polynomials of λ → arbitrary natural numbers n_e, n_h, n_s and d = n_h + n_e + n_s; reason: the statement holds for each λ separately, so it is the statement for all sizes
--   - encoding: outcomes of a measurement that 'always' lie in a coset → every basis vector with nonzero amplitude lies in the coset; reason: an outcome has positive probability exactly when some amplitude is nonzero
--   - reading: equality of distributions of tuples containing the state |Ψ⟩ → equality of the distributions of the tuples with the state recorded as its density matrix |Ψ⟩⟨Ψ|, expressed as equal expectations of every real test function; reason: a quantum state is a ray; for finite uniform samples, equal expectations of all test functions is equality of distributions
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Fact 4.5, pp.27–28

import Definitions.Def_QubitTracking_anchorVec

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- **Fact 4.5** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Fact 4.5, pp.27–28). Let
`(sk, |Ψ^{sk}_{n_e,n_h,n_s}⟩) ← GenAnchorState_{n_e,n_h,n_s}(1^λ)`, the vessel having
`d = n_h + n_e + n_s` qubits.
1. The standard-basis measurement on the vessel always outputs a vector in `T + v`.
2. The Hadamard-basis measurement on the vessel always outputs a vector in `S^⊥ + u`.
3. The distributions
   `{S, T, u, v, |Ψ^{sk}_{n_e,n_h,n_s}⟩ : sk ← GenAnchorState_{n_e,n_h,n_s}}` and
   `{T^⊥, S^⊥, v, u, (H^{⊗n_e}_𝐀 ⊗ H^{⊗(n_e+n_h+n_s)}_𝐁)|Ψ^{sk}_{n_e,n_s,n_h}⟩ : sk ← GenAnchorState_{n_e,n_s,n_h}}`
   are equal.

**Formalization Note** `GenAnchorState` samples `U_shift`, `u′`, `v′` uniformly (`anchorVec`).
Clauses 1–2 say every outcome of positive probability lies in the coset. In clause 3 a state is
recorded as its density matrix `|Ψ⟩⟨Ψ|`, and equality of distributions is equality of the expectations
of every real test function. -/
theorem fact_4_5 (ne nh ns d : ℕ) (hd : nh + ne + ns = d) :
    (∀ (U : GL (Fin d) (ZMod 2)) (u' : Bits (Fin nh)) (v' : Bits (Fin ns)) (x : Bits (Fin ne))
        (b : Bits (Fin d)),
        anchorVec ne nh ns U u' v' (x, b) ≠ 0 → b - anchorV nh ne ns U v' ∈ anchorT nh ne U) ∧
    (∀ (U : GL (Fin d) (ZMod 2)) (u' : Bits (Fin nh)) (v' : Bits (Fin ns)) (x : Bits (Fin ne))
        (z : Bits (Fin d)),
        (∑ b, hadamard (Fin d) z b * anchorVec ne nh ns U u' v' (x, b)) ≠ 0 →
          z - anchorU nh ne ns U u' ∈ perp (anchorS nh U)) ∧
    (∀ F : Submodule (ZMod 2) (Bits (Fin d)) × Submodule (ZMod 2) (Bits (Fin d)) × Bits (Fin d) ×
        Bits (Fin d) × Matrix (Bits (Fin ne) × Bits (Fin d)) (Bits (Fin ne) × Bits (Fin d)) ℂ → ℝ,
      avg (fun ω : GL (Fin d) (ZMod 2) × Bits (Fin nh) × Bits (Fin ns) =>
          F (anchorS nh ω.1, anchorT nh ne ω.1, anchorU nh ne ns ω.1 ω.2.1,
            anchorV nh ne ns ω.1 ω.2.2, proj (anchorVec ne nh ns ω.1 ω.2.1 ω.2.2))) =
        avg (fun ω : GL (Fin d) (ZMod 2) × Bits (Fin ns) × Bits (Fin nh) =>
          F (perp (anchorT ns ne ω.1), perp (anchorS ns ω.1), anchorV ns ne nh ω.1 ω.2.2,
            anchorU ns ne nh ω.1 ω.2.1,
            proj (kroneckerMap (· * ·) (hadamard (Fin ne)) (hadamard (Fin d)) *ᵥ
              anchorVec ne ns nh ω.1 ω.2.1 ω.2.2)))) := by sorry

end QubitTracking
