-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_7
-- name    : PrettyGoodShadow.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:34.551001+00:00
-- url     : https://prove2.me/theorems/31083edf-daf3-4a50-9f03-0a44d24c4e9d
-- title:
--   Lemma 4.7 — error probability bounded by the relative entropy of Bernoulli states
-- statement:
--   Let $0\preceq A\preceq I$, fix a label $x$, and let $\hat x$ be a label estimator with an arbitrary law on $\mathcal L$. Let $\varepsilon>0$ and $k\ge1$. Then
--
--   $$
--   \Pr_{\hat x}\big[|\operatorname{tr}(A\rho_{\hat x})-\operatorname{tr}(A\rho_x)|>\varepsilon\big]\le4e^{-k\varepsilon^2/2}+\sqrt{\tfrac12D\big(B_x^{\otimes k}\,\big\|\,B^{(k)}_{\hat x}\big)}.
--   $$
--
--   The statement is entirely classical, and it translates the error of any estimator into a relative entropy between Bernoulli states.
--
--   **Formalization Note** Natural logarithm. $0\preceq A\preceq I$ is the standing assumption of §4.1.
--
--   Differences from the source:
--   - encoding: D may be +∞, in which case the bound is vacuous → hypothesis D ≠ ⊤ and D.toReal in the bound; reason: the excluded case is exactly the vacuous one, and the guard rules out the junk value ⊤.toReal = 0
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.7, p.21 (restated p.22)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_Delta

namespace PrettyGoodShadow

open ShadowTomography.UpperBound (tensorPow)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Lemma 4.7** (arXiv:2610.06781, sha256 bd055b7d…, p.21, restated p.22). Fix a label `x` and a label estimator
`x̂` with any law `lam` on `L`. For an observable `0 ⪯ A ⪯ I` (§4.1, p.19),
`Pr_x̂[|tr(A ρ_x̂) − tr(A ρ_x)| > ε] ≤ 4 e^{−kε²/2} + √(½ D(B_x^{⊗k} ∥ B^{(k)}_x̂))`.

**Formalization Note** `lam` is an arbitrary probability vector, not the PGM's law ("any distribution", p.21).
Where the relative entropy is `+∞` the page's bound is vacuous; so the `.toReal` is taken under `D ≠ ⊤`, which
rules out the junk value `⊤.toReal = 0`. Natural logarithm. -/
theorem lemma_4_7 {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ) (hA : QAlgorithms.IsEffect A)
    (lam : L → ℝ) (hlam0 : ∀ y, 0 ≤ lam y) (hlam1 : ∑ y, lam y = 1) (x : L) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 1 ≤ k)
    (hD : relativeEntropy (tensorPow (bern (obs A (ρ x))) k) (bernMix A ρ lam k) ≠ ⊤) :
    ∑ y with ε < |obs A (ρ y) - obs A (ρ x)|, lam y ≤
      4 * Real.exp (-((k : ℝ) * ε ^ 2) / 2) +
        Real.sqrt ((1 / 2) *
          (relativeEntropy (tensorPow (bern (obs A (ρ x))) k) (bernMix A ρ lam k)).toReal) := by sorry

end PrettyGoodShadow
