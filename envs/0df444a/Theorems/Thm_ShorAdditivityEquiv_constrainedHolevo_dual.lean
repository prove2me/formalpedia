-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_constrainedHolevo_dual
-- name    : ShorAdditivityEquiv.constrainedHolevo_dual
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:57.397093+00:00
-- url     : https://prove2.me/theorems/2759db71-98a0-482e-9d61-865efedf6285
-- title:
--   Eqs. (12)–(13), p. 11 — LP dual of the constrained capacity: $\chi_N(\rho)=H(N(\rho))-\max_f f(\rho)$
-- statement:
--   Let $N$ be a quantum channel with input space $\mathcal H_{\mathrm{in}}$ and $\rho$ a density matrix on $\mathcal H_{\mathrm{in}}$. Call a linear function $f(X)=\mathrm{Tr}\,\tau X$, $\tau$ Hermitian, **feasible** if
--   $$
--   f(|v\rangle\langle v|) \le H\big(N(|v\rangle\langle v|)\big)\quad\text{for every unit vector } |v\rangle \text{ in the support of } \rho .
--   $$
--   Then the maximum of $f(\rho)$ over feasible $f$ exists and
--   $$
--   \chi_N(\rho) = H\big(N(\rho)\big) - \max_f f(\rho). \tag{12–13}
--   $$
--   Precisely: (a) some feasible $f$ satisfies $\chi_N(\rho)=H(N(\rho))-f(\rho)$, and (b) every feasible $f$ has $f(\rho)\le H(N(\rho))-\chi_N(\rho)$.
--
--   When $\rho$ has full rank its support is all of $\mathcal H_{\mathrm{in}}$ and the constraint is the paper's "for all $|v\rangle\in\mathcal H_{\mathrm{in}}$"; this is the case the paper proves by linear programming duality. For rank-deficient $\rho$ the constraint is imposed on the support only, following the paper's observation "that the only values of the function $f$ which are relevant in this case are those in the support of $\rho$". The dual function is the main tool of §§6–7.
--
--   Differences from the source:
--   - reading: (12)–(13) at a ρ that is not full rank, with the constraint of (13) for all |v⟩ ∈ H_in ("can be proved by using the observation that the only values of the function f which are relevant in this case are those in the support of ρ") → the constraint of (13) for the unit vectors v in the range of ρ (v.ofLp ∈ LinearMap.range ρ.mulVecLin); at full-rank ρ the range is all of H_in and the statement is literally (12)–(13); reason: the paper proves only the full-rank case and sketches the rest by restricting f to the support; attainment of a τ feasible on all of H_in at a boundary ρ is not established by the paper (the entropy is not Lipschitz there) and is not claimed
--   - encoding: linear functions f(ρ) = Tr τρ, maximum over f → τ Hermitian and f(X) = Re Tr(τ X); the max is stated as existence of an optimal τ (a) plus the bound for every feasible τ' (b); reason: a linear function real on Hermitian matrices is Re Tr(τ ·) with τ Hermitian; (a)+(b) is exactly "the maximum exists and equals H(N(ρ)) − χN(ρ)"
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §5, Eqs. (12)–(13), p. 11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ShorAdditivityEquiv_constrainedHolevo

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §5, Eqs. (12)–(13), p.11: "χN(ρ) = H(N(ρ)) − f(ρ) (12) where f is the linear function
defined by the maximization max_f f(ρ) such that f(|v⟩⟨v|) ≤ H(N(|v⟩⟨v|)) for all |v⟩ ∈ Hin,
(13) Here Hin is the input space for N and the maximum is taken over all linear functions
f(ρ) = Tr τρ. Eqs. (12) and (13) can be proved if ρ is full rank by using the duality theorem of
linear programming. [...] The case where ρ is not full rank can be proved by using the
observation that the only values of the function f which are relevant in this case are those in
the support of ρ."

Both halves of the claim are stated, for every density matrix `ρ`: (a) the maximum in (13) is
attained by some feasible `f = Tr τ ·` and its value is `H(N(ρ)) − χ_N(ρ)`; (b) every feasible
`f` has `f(ρ)` at most that value.

**Formalization Note.** The constraint of (13) ranges over the unit vectors `v` in the support
of `ρ`, i.e. the range of `ρ` (`v.ofLp ∈ LinearMap.range ρ.mulVecLin`). If `ρ` has full rank the
range is all of `H_in`, and the statement is literally (12)–(13) with "for all |v⟩ ∈ H_in". If
`ρ` is rank deficient this is the paper's own remark that only the values of `f` on the support
are relevant. The attainment of a `τ` feasible on all of `H_in` at a rank-deficient `ρ` is not
claimed, since that remark does not give it. The real linear functions on Hermitian matrices
are `f(X) = Re Tr(τ X)` with `τ` Hermitian (for Hermitian `τ` and `X` the trace is already
real). `|v⟩⟨v|` is `pureDensity v`. `N` is a channel (`IsChannel`). -/
theorem constrainedHolevo_dual {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (N : Superop I O) (hN : IsChannel N) (ρ : Matrix I I ℂ)
    (hρ : IsDensityMatrix ρ) :
    (∃ τ : Matrix I I ℂ, τ.IsHermitian ∧
      (∀ v : EuclideanSpace ℂ I, ‖v‖ = 1 → v.ofLp ∈ LinearMap.range ρ.mulVecLin →
        (τ * pureDensity v).trace.re ≤ vnEntropy (N (pureDensity v))) ∧
      constrainedHolevo N ρ = vnEntropy (N ρ) - (τ * ρ).trace.re) ∧
    (∀ τ' : Matrix I I ℂ, τ'.IsHermitian →
      (∀ v : EuclideanSpace ℂ I, ‖v‖ = 1 → v.ofLp ∈ LinearMap.range ρ.mulVecLin →
        (τ' * pureDensity v).trace.re ≤ vnEntropy (N (pureDensity v))) →
      (τ' * ρ).trace.re ≤ vnEntropy (N ρ) - constrainedHolevo N ρ) := by sorry

end ShorAdditivityEquiv
