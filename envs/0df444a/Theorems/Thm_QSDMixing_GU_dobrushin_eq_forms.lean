-- Prove2me | Theorems.Thm_QSDMixing_GU_dobrushin_eq_forms
-- name    : QSDMixing.GU.dobrushin_eq_forms
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:53:55.406483+00:00
-- url     : https://prove2.me/theorems/5c658ff4-339b-4270-a475-6136162c4a39
-- title:
--   §2.3.2, eq. (51) — equivalent forms of the quantum Dobrushin coefficient
-- statement:
--   Let $\mathcal A$ be a unital $*$-subalgebra of $M_n(\mathbb C)$ and let $T$ be a linear map sending $\mathcal D(\mathcal A)$ into itself. Then
--
--   $$
--   \kappa(T)=\frac12\sup_{\rho,\sigma\in\mathcal D(\mathcal A)}\|T(\rho)-T(\sigma)\|_1=\sup_{\substack{B=B^\dagger\in\mathcal A,\ \mathrm{tr}(B)=0\\ B\ne0}}\frac{\|T(B)\|_1}{\|B\|_1}.
--   $$
--
--   These forms are the ones used to bound $\kappa$ from a state pair and from a single traceless operator.
--
--   **Formalization Note** If $\mathcal D(\mathcal A)$ has at most one point, all three expressions are $0$.
--
--   Differences from the source:
--   - generalization: T : A → A a quantum channel → T a ℂ-linear map on M_n(ℂ) with T(D(A)) ⊆ D(A); reason: every channel on A qualifies after composing with a linear projection onto A, so this specializes to the source's claim; the proof uses only these properties
--   - encoding: a finite-dimensional unital C*-subalgebra A → a StarSubalgebra of M_n(ℂ), with D(A) its positive semidefinite trace-one elements; reason: the same object, with the ambient matrix algebra named; Mathlib's StarSubalgebra contains the identity
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, eq. (51), p.15

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QSDMixing_GU_densityIn
import Definitions.Def_QSDMixing_GU_dobrushin

set_option autoImplicit false

namespace QSDMixing.GU

/-- **§2.3.2, eq. (51), p.15.** The equivalent forms of the quantum Dobrushin coefficient:
`κ(T) = (1/2) sup_{ρ,σ ∈ D(A)} ‖T ρ - T σ‖₁ = sup_{B = B† ∈ A, tr B = 0, B ≠ 0} ‖T B‖₁ / ‖B‖₁`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, eq. (51), p.15.

**Formalization Note.** `T : A → A` a quantum channel in the page is generalized to a `ℂ`-linear map on `M_n(ℂ)`
sending `D(A)` into `D(A)`. A channel on `A` extends to such a map by composing with a linear projection onto `A`.
`A` is a `StarSubalgebra`, hence unital, as the page requires. If `D(A)` has at most one point, every form is `0`
(`sSup ∅ = 0`, `sSup {0} = 0`). -/
theorem dobrushin_eq_forms {n : Type} [Fintype n] [DecidableEq n]
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hT : ∀ ρ ∈ densityIn A, T ρ ∈ densityIn A) :
    dobrushin A T = (1 / 2) * sSup {r | ∃ ρ ∈ densityIn A, ∃ σ ∈ densityIn A,
        r = WildeQIT.traceNorm (T ρ - T σ)} ∧
    dobrushin A T = sSup {r | ∃ B ∈ A, B.IsHermitian ∧ B.trace = 0 ∧ B ≠ 0 ∧
        r = WildeQIT.traceNorm (T B) / WildeQIT.traceNorm B} := by sorry

end QSDMixing.GU
