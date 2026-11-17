-- Prove2me | Theorems.Thm_QSDMixing_GU_Supplement_stabilized_dobrushin_characterization
-- name    : QSDMixing.GU.Supplement.stabilized_dobrushin_characterization
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:43:33.861626+00:00
-- url     : https://prove2.me/theorems/42696533-3a28-4be3-8b34-4a4a00f9b818
-- title:
--   Theorem 8 — stabilized Dobrushin characterization
-- statement:
--   Let $\epsilon\in(0,1/2)$. There is a constant $C=C(\epsilon)>0$, independent of the finite-dimensional uniform mixed-state ensemble, such that the following holds whenever distinct states have fidelity below one. If $\widetilde\kappa_{\mathrm{gen}}$ is formed from the ancillary-stabilized trace-norm contraction coefficients of the inhomogeneous channels $\Phi_s$, then $\widetilde\kappa_{\mathrm{gen}}<1$, all relevant copy counts are finite, and
--
--   $$
--   k_{\mathrm{wc}}\le C\frac1{1-\widetilde\kappa_{\mathrm{gen}}},
--   \qquad
--   \frac1{1-\widetilde\kappa_{\mathrm{gen}}}\le Ck_{\mathrm{wc}}.
--   $$
--
--   Moreover, the complete chain is
--
--   $$
--   t_{\min}(4\sqrt\epsilon)\le k_{\min}(\epsilon)
--     \le t_{\min}(\epsilon)\le Ck_{\mathrm{wc}}(\epsilon).
--   $$
--
--   These inequalities state $k_{\mathrm{wc}}=\Theta_\epsilon(1/(1-\widetilde\kappa_{\mathrm{gen}}))$ and the $O_\epsilon(k_{\mathrm{wc}})$ clause of equation (33) with constants depending only on $\epsilon$.
--
--   Differences from the source:
--   - reading: $\Theta_\epsilon$ and $O_\epsilon$ → one positive constant chosen after $\epsilon$ and before the ensemble, with every comparison written as an inequality; reason: taking the maximum of the finitely many source constants yields one ensemble-uniform factor
--   - encoding: $\eta(T)=\sup_R\widetilde\kappa(T\otimes\mathrm{id}_R)$ → a supremum over ancillary spaces $\mathbb C^r$ for all positive integers $r$, Hermitian nonzero inputs, and literal zero diagonal blocks; reason: every finite-dimensional ancillary system is unitarily some $\mathbb C^r$
--   - encoding: $\Phi_s=\mathcal N_s\circ\cdots\circ\mathcal N_1$ → its direct matrix action multiplying each block by $(S_i^\dagger S_j)^{\otimes s}$; reason: this is exactly the composite specified by equations (162)–(164)
--   - encoding: asymptotic comparisons of possibly undefined reciprocal gaps or infinite minima → $\widetilde\kappa_{\mathrm{gen}}<1$ and finite natural witnesses are conclusions; reason: Lean's real division by zero and total infima would otherwise trivialize the statement
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 8, pp.33–34, eqs. (32)–(33)

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QSDMixing_GU_kMin
import Definitions.Def_QSDMixing_GU_kWc
import Definitions.Def_QSDMixing_GU_Supplement_MixedEnsembleFactorization

set_option autoImplicit false

namespace QSDMixing.GU.Supplement

/-- **Theorem 8, pp.33--34.** Uniformly for `ε∈(0,1/2)`, worst-case discrimination
sample complexity is comparable to the reciprocal gap of the stabilized generalized Dobrushin
coefficient. The same ensemble-independent constant also records the complete chain
`t_min(4√ε) ≤ k_min(ε) ≤ t_min(ε) ≤ O_ε(k_wc)`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state
discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 8,
pp.33--34, eqs. (32)--(33). -/
theorem stabilized_dobrushin_characterization (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type) [Fintype I] [Nonempty I] (d : ℕ)
        (E : MixedEnsembleFactorization I d),
        (∀ i j, i ≠ j →
          WildeQIT.fidelity (mixedStateMatrix (E.state i)) (mixedStateMatrix (E.state j)) < 1) →
        let κ := stabilizedDobrushinGen E
        κ < 1 ∧
        ∃ km tm tw : ℕ,
          QSDMixing.GU.kMin E.state ε = km ∧
          mixedWeakMixingTime E ε = tm ∧
          mixedWeakMixingTime E (4 * Real.sqrt ε) = tw ∧
          ∃ kw : ℕ,
            QSDMixing.GU.kWc E.state ε = kw ∧
            (tw : ℝ) ≤ km ∧ (km : ℝ) ≤ tm ∧ (tm : ℝ) ≤ C * kw ∧
            (kw : ℝ) ≤ C * (1 / (1 - κ)) ∧ 1 / (1 - κ) ≤ C * kw := by sorry

end QSDMixing.GU.Supplement
