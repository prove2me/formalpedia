-- Prove2me | Theorems.Thm_QSDMixing_GU_Supplement_dual_hypergroup_reduction
-- name    : QSDMixing.GU.Supplement.dual_hypergroup_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:41:12.486825+00:00
-- url     : https://prove2.me/theorems/ddde6b8f-7d93-4225-ba20-69795b335a5e
-- title:
--   Theorem 4 — dual-hypergroup reduction
-- statement:
--   Let $G$ be finite, let $U$ be a unitary representation, let $\psi$ be a unit vector with stabilizer $H$, and suppose the Hecke algebra $\mathcal A=\operatorname{End}_G(\mathbb C[G/H])$ is commutative. Put $n=|G/H|$ and let $X$ be the coset Gram matrix.
--
--   There are primitive-idempotent data for the dual hypergroup $\widehat\Omega$ and a bijection
--
--   $$
--   p:\{Y\in\mathcal A:Y\succeq0,\ \operatorname{tr}Y=n\}\longrightarrow\mathcal P(\widehat\Omega)
--   $$
--
--   whose inverse sends $q$ to $n\Xi(q)=n\sum_i(q_i/m_i)E_i$. If $\pi_i=m_i/n$ is the Haar law, then for every integer $t\ge0$,
--
--   $$
--   \frac12\bigl\|\Phi_X^t(\tau_n)-\omega_n\bigr\|_1
--     =d_{\mathrm{TV}}\bigl(p(X)^{*t},\pi\bigr).
--   $$
--
--   Hence the quantum mixing time at trace-norm tolerance $\epsilon$ equals the classical total-variation mixing time at tolerance $\epsilon/2$.
--
--   Differences from the source:
--   - encoding: the page's already-constructed dual hypergroup and primitive idempotents → an existential `HeckeDualData` package recording the primitive decomposition, Krein formula, hypergroup laws, and Haar law; reason: the package states the same constructed object without assuming the theorem's bijection or mixing identity
--   - encoding: positive matrices of trace $n$ → complex positive-semidefinite matrices with complex trace equal to $n$; reason: this is the finite-dimensional Loewner-order meaning of the source condition
--   - encoding: “reduces to a classical total-variation mixing time” → quantum tolerance $\epsilon$ equals classical total-variation tolerance $\epsilon/2$; reason: equation (19) has the explicit factor $1/2$, while the base quantum definition thresholds the unhalved trace norm
--   - reading: unstated range of the mixing-time minimum → integers $t\ge1$ with value $\infty$ if no time qualifies; reason: the paper's $\mathbb N$ convention in equation (52) starts at one
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 4, p.20, eqs. (18)–(19)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_hecke
import Definitions.Def_QSDMixing_GU_schurChannel
import Definitions.Def_QSDMixing_GU_tauN
import Definitions.Def_QSDMixing_GU_omegaN
import Definitions.Def_QSDMixing_GU_tMin
import Definitions.Def_QSDMixing_GU_Supplement_HeckeDualData

set_option autoImplicit false
open GaussTesting (Ell2)
open scoped MatrixOrder ComplexOrder

namespace QSDMixing.GU.Supplement

/-- **Theorem 4, p.20.** In the Gelfand-pair case, positive trace-`n` elements of the
commutative Hecke algebra are in bijection with probability measures on the dual hypergroup.
The map is the primitive-idempotent map `Ξ`, trace distance is twice total variation, and the
Schur-channel walk becomes convolution by the Gram-matrix law. Consequently its fixed-state
quantum mixing time is the classical total-variation mixing time.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state
discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorem 4, p.20,
eqs. (18)--(19). -/
theorem dual_hypergroup_reduction {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1)
    (hcomm : ∀ A B : QSDMixing.GU.hecke (QSDMixing.GU.stabilizer U ψ), A * B = B * A) :
    let H := QSDMixing.GU.stabilizer U ψ
    let n : ℝ := Fintype.card (G ⧸ H)
    ∃ (Ω : Type) (_ : Fintype Ω) (D : HeckeDualData H Ω)
      (p : {Y : Matrix (G ⧸ H) (G ⧸ H) ℂ //
          Y ∈ QSDMixing.GU.hecke H ∧ Y.PosSemidef ∧
            Matrix.trace Y = (n : ℂ)} ≃ FiniteProbability Ω)
      (hXmem : QSDMixing.GU.gram U ψ ∈ QSDMixing.GU.hecke H)
      (hXpos : (QSDMixing.GU.gram U ψ).PosSemidef)
      (hXtr : Matrix.trace (QSDMixing.GU.gram U ψ) = (n : ℂ)),
      (∀ q : FiniteProbability Ω, (p.symm q).1 = (n : ℂ) • D.xi q) ∧
      (∀ t : ℕ,
        (1 / 2 : ℝ) * WildeQIT.traceNorm
            ((QSDMixing.GU.schurChannel (QSDMixing.GU.gram U ψ))^[t]
              QSDMixing.GU.tauN - QSDMixing.GU.omegaN) =
          totalVariation
            (D.convolutionPower (p ⟨QSDMixing.GU.gram U ψ, hXmem, hXpos, hXtr⟩) t) D.haar) ∧
      ∀ ε : ℝ,
        QSDMixing.GU.tMin U ψ ε =
          D.mixingTime (p ⟨QSDMixing.GU.gram U ψ, hXmem, hXpos, hXtr⟩) (ε / 2) := by sorry

end QSDMixing.GU.Supplement
