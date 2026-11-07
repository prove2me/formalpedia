-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_3_2
-- name    : PrettyGoodShadow.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:16.862064+00:00
-- url     : https://prove2.me/theorems/70c4ea7a-dec9-4776-943c-d9889e877712
-- title:
--   Lemma 3.2 — $\operatorname{tr}(\sigma(\log X-\log S))\le\log\operatorname{tr}(\sigma D_S(X))$
-- statement:
--   Let $\sigma$ be a quantum state and let $X\succeq0$ satisfy $\operatorname{supp}(\sigma)\subseteq\operatorname{supp}(X)\subseteq\operatorname{supp}(S)$. Then
--
--   $$
--   \operatorname{tr}\big(\sigma(\log X-\log S)\big)\le\log\operatorname{tr}\big(\sigma D_S(X)\big).
--   $$
--
--   This is the main property of the integral pretty good measurement used in the analysis: it bounds a difference of logarithms by the logarithm of an outcome probability.
--
--   **Formalization Note** Logarithms are taken on supports, through functional calculus with $\log0=0$. Support inclusion is the published kernel condition.
--
--   Differences from the source:
--   - generalization: S is the average state S(p, n) → S is any positive semidefinite operator; reason: the proof uses only that S is positive definite on its support, and S(p, n) is one such operator
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 3.2, p.16

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_PrettyGoodShadow_divS

open scoped ComplexOrder

namespace PrettyGoodShadow

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported)

/-- **Lemma 3.2** (arXiv:2610.06781, sha256 bd055b7d…, p.16). Let `σ` be a quantum state and let `X ⪰ 0` satisfy
`supp(σ) ⊆ supp(X) ⊆ supp(S)`. Then `tr(σ · (log X − log S)) ≤ log tr(σ · D_S(X))`.

**Formalization Note** `log` is `cfc Real.log`, the logarithm on the support and `0` off it. Support inclusion is
the published `IsSupported`, the reverse inclusion of kernels. The logarithm on the right has a positive argument
under these hypotheses. `S` is any positive semidefinite operator, and is nonzero since `σ` is. -/
theorem lemma_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] (σ X S : Matrix ι ι ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (hX : X.PosSemidef) (hS : S.PosSemidef)
    (hσX : IsSupported σ X) (hXS : IsSupported X S) :
    (σ * (cfc Real.log X - cfc Real.log S)).trace.re ≤ Real.log (σ * divS S X).trace.re := by sorry

end PrettyGoodShadow
