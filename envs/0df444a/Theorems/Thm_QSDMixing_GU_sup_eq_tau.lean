-- Prove2me | Theorems.Thm_QSDMixing_GU_sup_eq_tau
-- name    : QSDMixing.GU.sup_eq_tau
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:29.433828+00:00
-- url     : https://prove2.me/theorems/6ea7f8c9-4385-411e-83ff-92acde032f0a
-- title:
--   Proposition 14 — $\tau_n$ is a worst initial state
-- statement:
--   For a geometrically uniform ensemble on $G/H$, with Gram matrix $X$ and Hecke algebra $\mathcal A$, and for every $t$,
--
--   $$
--   \sup_{\rho\in\mathcal D(\mathcal A)}\|\Phi_X^t(\rho)-\omega_n\|_1=\|\Phi_X^t(\tau_n)-\omega_n\|_1.
--   $$
--
--   Thus the mixing time $t_{\min}$ from the fixed state $\tau_n$ equals the worst-case mixing time $t_{\mathrm{mix}}(\Phi_X|_{\mathcal A},\omega_n,\epsilon)$.
--
--   Differences from the source:
--   - generalization: t ∈ ℕ, the paper's ℕ being {1, 2, …} → every natural number t, including t = 0; reason: the same proof applies at t = 0, and the statement specializes to the source's range
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - encoding: the channel T = Φ_X|_A on the algebra A → the map Φ_X on all of M_n(ℂ), with the suprema taken over D(A); reason: Φ_X preserves A, and only its values on D(A) enter
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.1, Proposition 14, eq. (74), p.18

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_hecke
import Definitions.Def_QSDMixing_GU_densityIn
import Definitions.Def_QSDMixing_GU_schurChannel
import Definitions.Def_QSDMixing_GU_tauN
import Definitions.Def_QSDMixing_GU_omegaN

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **Proposition 14, p.18.** The all-one state `τ_n` is a worst initial state for the Hadamard channel on the Hecke algebra:
for every `t`, `sup_{ρ ∈ D(A)} ‖T^t ρ - ω_n‖₁ = ‖T^t τ_n - ω_n‖₁`, with `T = Φ_X|_A`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.1, Proposition 14, eq. (74), p.18.

**Formalization Note.** `t` ranges over all of `ℕ`, including `t = 0`, where the same proof applies; the paper's `ℕ` is `{1, 2, …}`
(its eq. (52)). -/
theorem sup_eq_tau {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) (t : ℕ) :
    sSup {r | ∃ ρ ∈ densityIn (hecke (stabilizer U ψ)),
        r = WildeQIT.traceNorm ((schurChannel (gram U ψ))^[t] ρ - omegaN)} =
      WildeQIT.traceNorm ((schurChannel (gram U ψ))^[t] tauN - omegaN) := by sorry

end QSDMixing.GU
