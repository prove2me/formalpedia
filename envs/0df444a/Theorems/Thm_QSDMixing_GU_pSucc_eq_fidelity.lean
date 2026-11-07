-- Prove2me | Theorems.Thm_QSDMixing_GU_pSucc_eq_fidelity
-- name    : QSDMixing.GU.pSucc_eq_fidelity
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:00:43.765212+00:00
-- url     : https://prove2.me/theorems/772ae4e1-3770-489b-a653-2aa7763be07d
-- title:
--   §3, eq. (66), coset form — the PGM is optimal, with closed form and fidelity form
-- statement:
--   Let $G$ be a finite group with a unitary representation $U$ on a Hilbert space, let $\psi$ be a unit vector with stabilizer $H$, let $n=|G/H|$, and let $X$ be the Gram matrix of the states $|\psi_{gH}\rangle$. For every $t\ge1$, the optimal average success probability for discriminating $t$ i.i.d. copies with uniform prior is attained and equals the value of the pretty good measurement, and
--
--   $$
--   p^*_{\mathrm{succ}}(t)=p_{\mathrm{PGM}}(t)=\frac1{n^2}\big(\mathrm{tr}\sqrt{X_t}\big)^2=F\big(\Phi_X^t(\tau_n),\omega_n\big),
--   $$
--
--   where $X_t=X^{\circ t}$ and $F$ is the squared fidelity.
--
--   This identifies the sample complexity with a fidelity-based mixing time of the Hadamard channel. No bound on the overlaps is assumed.
--
--   **Formalization Note** The first clause is that $p_{\mathrm{PGM}}(t)$ is the greatest element of the set of average successes of POVMs. On the page, $\Phi_X^t(\tau_n)$ is written $\frac1{|G|}X_t$.
--
--   Differences from the source:
--   - reading: eq. (66) on the ensemble over G, with |G|; p.17 says the arguments "still apply" on G/H → the coset form on G/H, with n = |G/H|; reason: this is the form the page transfers to and the goal uses
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - reading: "t-copy", with t unstated → t ≥ 1; reason: the same convention as every minimum in the paper; see `kMin`
--   - encoding: max over POVMs → IsGreatest of the set of POVM values; reason: this states attainment and the value of the maximum together
--   - encoding: pure states |ψ_{gH}⟩ with uniform prior → MixedState.pure of U_{x.out} ψ, the prior 1/n built into kMin; reason: the vector does not depend on the representative, because U_h ψ = ψ on H
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, eq. (66), and the transfer to G/H, p.17

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_tensorVec
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_IsPOVM
import Definitions.Def_QSDMixing_GU_copyEffect
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_cosetEnsemble
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_gramPow
import Definitions.Def_QSDMixing_GU_schurChannel
import Definitions.Def_QSDMixing_GU_tauN
import Definitions.Def_QSDMixing_GU_omegaN
import Definitions.Def_QSDMixing_GU_pgmSuccess

set_option autoImplicit false
open scoped MatrixOrder
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **§3, eq. (66), coset form, p.17.** For a geometrically uniform pure-state ensemble on `G ⧸ H` and
`t ≥ 1` copies, the pretty good measurement is optimal, and
`p*_succ(t) = p_PGM(t) = (1/n²) (tr √X_t)² = F(Φ_X^t(τ_n), ω_n)`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, eq. (66), p.17, with the transfer to `G/H` stated on the same page.

**Formalization Note.** `IsGreatest` carries both the attainment of the maximum in (4) and the equality
`p*_succ = p_PGM`. Eq. (66) is printed on `G` with `|G|`; p.17 transfers it to `G/H` with `n = |G/H|`
("previous arguments … still apply"), and this is the form stated here. `F` is the squared fidelity
`WildeQIT.fidelity`, and `Φ_X^t(τ_n) = (1/n) X_t` is what the paper's `(1/|G|) X_t` becomes. -/
theorem pSucc_eq_fidelity {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) (t : ℕ) (ht : 1 ≤ t) :
    let n : ℝ := Fintype.card (G ⧸ stabilizer U ψ)
    let v : G ⧸ stabilizer U ψ → Ell2 (Fin t → ι) := fun x =>
      tensorVec fun _ => (U x.out : Ell2 ι →L[ℂ] Ell2 ι) ψ
    IsGreatest
        {p : ℝ | ∃ M : G ⧸ stabilizer U ψ → Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι), IsPOVM M ∧
          p = (1 / n) * ∑ x, copyEffect (cosetEnsemble U ψ hψ x) t (M x)}
        (pgmSuccess v) ∧
      pgmSuccess v = (Matrix.trace (CFC.sqrt (gramPow U ψ t))).re ^ 2 / n ^ 2 ∧
      pgmSuccess v = WildeQIT.fidelity ((schurChannel (gram U ψ))^[t] tauN) omegaN := by sorry

end QSDMixing.GU
