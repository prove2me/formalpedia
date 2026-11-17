-- Prove2me | Theorems.Thm_QSDMixing_GU_Supplement_mixed_state_weak_mixing_sandwich
-- name    : QSDMixing.GU.Supplement.mixed_state_weak_mixing_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:42:56.642026+00:00
-- url     : https://prove2.me/theorems/3eb9c347-d97c-415a-a4f7-49ae8d44e0da
-- title:
--   Theorem 7 — mixed-state weak-mixing sandwich
-- statement:
--   Let $(\rho_i)_{i\in I}$ be a nonempty finite uniform ensemble of mixed states on $\mathbb C^d$, with $\rho_i=S_iS_i^\dagger$ and $F(\rho_i,\rho_j)<1$ whenever $i\ne j$. Let $t_{\min}$ be the quantum weak mixing time defined from the block Gram matrices $X_t=[(S_i^\dagger S_j)^{\otimes t}]_{i,j}$ and their block pinching.
--
--   For every $\epsilon\in(0,1)$,
--
--   $$
--   t_{\min}(4\sqrt\epsilon)\le k_{\min}(\epsilon)\le t_{\min}(\epsilon).
--   $$
--
--   Thus the exact tolerance $4\sqrt\epsilon$ gives the lower side of the sample-complexity sandwich without assuming geometrical uniformity or purity.
--
--   Differences from the source:
--   - encoding: finite-dimensional density matrices $\rho_i=S_iS_i^\dagger$ → base-mission countable-mixture states on $\ell^2(\operatorname{Fin}d)$ together with square matrix factors whose products equal their density matrices; reason: every finite-dimensional density matrix has such a mixture and square-root factor
--   - encoding: a finite uniform ensemble of $n$ states → a nonempty finite label type $I$ with the factor $1/|I|$ built into $k_{\min}$ and the weak mixing time; reason: nonemptiness is the domain condition for the displayed normalization by $n$
--   - reading: unstated copy-count lower endpoint → integers at least one and $\mathbb N\cup\{\infty\}$-valued minima; reason: this is the paper's natural-number convention and avoids the empty-set value of natural-number infima
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 7, p.32, eq. (31)

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QSDMixing_GU_kMin
import Definitions.Def_QSDMixing_GU_Supplement_MixedEnsembleFactorization

set_option autoImplicit false

namespace QSDMixing.GU.Supplement

/-- **Theorem 7, p.32.** For every nonempty finite uniform ensemble of finite-dimensional mixed
states with pairwise fidelity below one, the block-Gram quantum weak mixing time sandwiches
minimum-error discrimination sample complexity with the exact tolerance `4√ε`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state
discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 7, p.32,
eq. (31). -/
theorem mixed_state_weak_mixing_sandwich {I : Type} [Fintype I] [Nonempty I] {d : ℕ}
    (E : MixedEnsembleFactorization I d)
    (hdistinct : ∀ i j, i ≠ j →
      WildeQIT.fidelity (mixedStateMatrix (E.state i)) (mixedStateMatrix (E.state j)) < 1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    mixedWeakMixingTime E (4 * Real.sqrt ε) ≤ QSDMixing.GU.kMin E.state ε ∧
      QSDMixing.GU.kMin E.state ε ≤ mixedWeakMixingTime E ε := by sorry

end QSDMixing.GU.Supplement
