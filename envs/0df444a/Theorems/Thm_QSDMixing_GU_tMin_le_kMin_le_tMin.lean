-- Prove2me | Theorems.Thm_QSDMixing_GU_tMin_le_kMin_le_tMin
-- name    : QSDMixing.GU.tMin_le_kMin_le_tMin
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:23.777948+00:00
-- url     : https://prove2.me/theorems/c211c885-b32f-4341-9736-e3b4c8b3d66c
-- title:
--   §3, eqs. (71)–(72) — Fuchs–van de Graaf sandwich, $t_{\min}(2\sqrt\epsilon)\le k_{\min}(\epsilon)\le t_{\min}(2-2\sqrt{1-\epsilon})$
-- statement:
--   For a geometrically uniform ensemble on $G/H$, set $d_t=\|\Phi_X^t(\tau_n)-\omega_n\|_1$. For every $t\ge1$,
--
--   $$
--   \frac{d_t^2}4\le1-F\big(\Phi_X^t(\tau_n),\omega_n\big)\le d_t-\frac{d_t^2}4,
--   $$
--
--   and for every $\epsilon\in(0,1)$,
--
--   $$
--   t_{\min}(2\sqrt\epsilon)\le k_{\min}(\epsilon)\le t_{\min}\big(2-2\sqrt{1-\epsilon}\big).
--   $$
--
--   This is the comparison of discrimination sample complexity with the trace-norm mixing time. No bound on the overlaps is assumed.
--
--   **Formalization Note** The second display is an inequality between values in $\mathbb N\cup\{\infty\}$. The tolerance $2\sqrt\epsilon$ may exceed $1$.
--
--   Differences from the source:
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - reading: minimum over an unstated range of k and t → minimum over k, t ≥ 1; reason: the paper's ℕ in (52) starts at 1 (eq. (15) writes s ≥ 1), and with t = 0 allowed Theorem 2 fails at A = ℂ·1; for n ≥ 2 the value does not change
--   - encoding: k_min, k_wc, t_min and t_mix as numbers → values in ℕ∞, with ⊤ when no count qualifies; reason: the minima can be over an empty set, where Lean's ℕ-valued sInf would give the junk value 0
--   - encoding: pure states |ψ_{gH}⟩ with uniform prior → MixedState.pure of U_{x.out} ψ, the prior 1/n built into kMin; reason: the vector does not depend on the representative, because U_h ψ = ψ on H
--   - encoding: max over POVMs at least 1 − ε → there exists a POVM reaching at least 1 − ε; reason: equivalent whenever the maximum exists, and it does not assume attainment
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, eqs. (71)–(72), pp.17–18

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_cosetEnsemble
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_kMin
import Definitions.Def_QSDMixing_GU_schurChannel
import Definitions.Def_QSDMixing_GU_tauN
import Definitions.Def_QSDMixing_GU_omegaN
import Definitions.Def_QSDMixing_GU_tMin

set_option autoImplicit false
open scoped MatrixOrder
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **§3, eqs. (71)–(72), pp.17–18.** The Fuchs–van de Graaf sandwich for the Hadamard channel, and the
resulting two-sided bound of `k_min` by `t_min`:
`d_t²/4 ≤ 1 - F(Φ_X^t(τ_n), ω_n) ≤ d_t - d_t²/4` with `d_t = ‖Φ_X^t(τ_n) - ω_n‖₁`, and
`t_min(2√ε) ≤ k_min(ε) ≤ t_min(2 - 2√(1 - ε))`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, eqs. (71)–(72), pp.17–18.

**Formalization Note.** The comparison is in `ℕ∞`, where all three values may be `⊤`. No bound on the overlaps is
assumed, since the page has none at this point. `2√ε` can exceed `1`, and `t_min` is then still defined. -/
theorem tMin_le_kMin_le_tMin {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) :
    (∀ t : ℕ, 1 ≤ t →
      let d := WildeQIT.traceNorm ((schurChannel (gram U ψ))^[t] tauN - omegaN)
      let F := WildeQIT.fidelity ((schurChannel (gram U ψ))^[t] tauN) omegaN
      d ^ 2 / 4 ≤ 1 - F ∧ 1 - F ≤ d - d ^ 2 / 4) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      tMin U ψ (2 * Real.sqrt ε) ≤ kMin (cosetEnsemble U ψ hψ) ε ∧
        kMin (cosetEnsemble U ψ hψ) ε ≤ tMin U ψ (2 - 2 * Real.sqrt (1 - ε)) := by sorry

end QSDMixing.GU
