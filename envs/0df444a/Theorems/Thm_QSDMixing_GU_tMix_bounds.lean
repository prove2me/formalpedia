-- Prove2me | Theorems.Thm_QSDMixing_GU_tMix_bounds
-- name    : QSDMixing.GU.tMix_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:44.133801+00:00
-- url     : https://prove2.me/theorems/d5c6c394-736d-4e9f-80c0-88450c82db07
-- title:
--   Theorem 2 — two-sided bound of $t_{\mathrm{mix}}$ by $\kappa_{\mathrm{gen}}$
-- statement:
--   Let $\mathcal A$ be a unital $*$-subalgebra of $M_n(\mathbb C)$, let $T$ be a linear map sending $\mathcal D(\mathcal A)$ into itself, and let $\omega\in\mathcal D(\mathcal A)$ with $T(\omega)=\omega$. Let $\epsilon\in(0,\frac12)$. If $\kappa_{\mathrm{gen}}(T)<1$, then $t_{\mathrm{mix}}(T,\omega,\epsilon)$ is finite and
--
--   $$
--   \frac{1-\epsilon}{1-\kappa_{\mathrm{gen}}(T)}\le t_{\mathrm{mix}}(T,\omega,\epsilon)\le\frac{1+\log(2/\epsilon)}{1-\kappa_{\mathrm{gen}}(T)}.
--   $$
--
--   So $1/(1-\kappa_{\mathrm{gen}})$ gives the scale of the mixing time at any fixed accuracy.
--
--   Differences from the source:
--   - generalization: T : A → A a quantum channel → T a ℂ-linear map on M_n(ℂ) with T(D(A)) ⊆ D(A); reason: every channel on A qualifies after composing with a linear projection onto A, so this specializes to the source's claim; the proof uses only these properties
--   - encoding: a finite-dimensional unital C*-subalgebra A → a StarSubalgebra of M_n(ℂ), with D(A) its positive semidefinite trace-one elements; reason: the same object, with the ambient matrix algebra named; Mathlib's StarSubalgebra contains the identity
--   - reading: minimum over an unstated range of k and t → minimum over k, t ≥ 1; reason: the paper's ℕ in (52) starts at 1 (eq. (15) writes s ≥ 1), and with t = 0 allowed Theorem 2 fails at A = ℂ·1; for n ≥ 2 the value does not change
--   - encoding: k_min, k_wc, t_min and t_mix as numbers → values in ℕ∞, with ⊤ when no count qualifies; reason: the minima can be over an empty set, where Lean's ℕ-valued sInf would give the junk value 0
--   - encoding: log → Real.log, the natural logarithm; reason: eq. (54) uses e^{−m(1−κ_s)}
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, Theorem 2, eq. (16), p.15

import Mathlib
import Definitions.Def_QSDMixing_GU_densityIn
import Definitions.Def_QSDMixing_GU_dobrushin
import Definitions.Def_QSDMixing_GU_dobrushinGen
import Definitions.Def_QSDMixing_GU_tMix

set_option autoImplicit false

namespace QSDMixing.GU

/-- **Theorem 2, p.15 (also p.6).** If `κ_gen(T) < 1` and `ε ∈ (0, 1/2)`, the mixing time is finite and
`(1 - ε) / (1 - κ_gen(T)) ≤ t_mix(T, ω, ε) ≤ (1 + log(2/ε)) / (1 - κ_gen(T))`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, Theorem 2, eq. (16), p.15.

**Formalization Note.** `T` is generalized as in `dobrushin_eq_forms`. `ω` is a stationary state in `D(A)`. `log` is natural, as
eq. (54) uses `e^{-m(1-κ_s)}`. `t` ranges over `t ≥ 1` (see `tMix`): if `t = 0` were allowed, the printed lower bound would fail at
`A = ℂ·1 ⊂ M_1`, `T = id`, where `D(A)` is a point, `κ_gen = 0` and `t_mix = 0 < 1 - ε`. -/
theorem tMix_bounds {n : Type} [Fintype n] [DecidableEq n]
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hT : ∀ ρ ∈ densityIn A, T ρ ∈ densityIn A) (ω : Matrix n n ℂ) (hω : ω ∈ densityIn A)
    (hωT : T ω = ω) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (hκ : dobrushinGen A T < 1) :
    ∃ t : ℕ, tMix A T ω ε = t ∧
      (1 - ε) / (1 - dobrushinGen A T) ≤ t ∧
      (t : ℝ) ≤ (1 + Real.log (2 / ε)) / (1 - dobrushinGen A T) := by sorry

end QSDMixing.GU
