-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_Supplement_theorem_3_1_counterexample
-- name    : RetirePartialInfo.Duality.Supplement.theorem_3_1_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:22:27.161367+00:00
-- url     : https://prove2.me/theorems/cfb7deb9-5eb1-4e14-8e78-a4d0ed4ceba8
-- title:
--   Theorem 3.1 (corrected: counterexample to global Sobolev existence for γ > 1)
-- statement:
--   The global Sobolev assertion in the printed theorem is false. For any admissible financial/HMM parameters with $\gamma>1$ and any finite $q\ge1$, there is no function satisfying the full displayed package:
--
--   $$\neg\exists v\in W_q^{1,2,2}(\mathcal M_T):\ (30),\ C^{1,2,2}(\overline{\mathcal M}_T),\ v_{yy}>0,\ v_y<0,\ \lim_{y\downarrow0}v_y=-\infty,\ \lim_{y\to\infty}v_y=0^-,\ |v_y|+|v_p|\le C(1+y^{-\kappa}).$$
--
--   Here $C,\kappa>0$ are uniform over all states. The negation retains the equation, terminal data, regularity, both limits and the entire growth estimate. Uniqueness is moot because the alleged class is empty. For a concrete allowed instance take $T=T_1=r=\sigma=\beta=\ell=\lambda_1=\lambda_2=1$, $\xi=0$, $\mu_1=2$, $\mu_2=0$, $\gamma=2$. This counterexample replaces the false existence claim; it does not assert a local substitute or discard the other source clauses silently.
--
--   **Formalization Note** The conjugate is still the published supremum of the actual CRRA utility. The limits and strict signs occur inside the negated existential package.
--
--   Differences from the source:
--   - correction: Global W_q existence/uniqueness for every CRRA regime → Negation of its full existence package on the allowed γ>1 regime; reason: Negative terminal conjugate, continuity and the claimed negative y derivative contradict the zeroth global L^q term; DISPROOF.md retains the source anchors and explicit instance
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 19, Theorem 3.1; p. 16, definition of W_q; p. 17, (30); pp. 35–36, Appendix A

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis

open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), p.19, Theorem 3.1; p.17, (30); pp.35–36, Appendix A.
**Formalization Note.** Counterexample to the printed global claim, not a local replacement.
For γ>1 the terminal conjugate is negative. Continuity near the terminal face and the
claimed negative y derivative force a negative lower bound on |v| on an infinite-y slab,
contradicting even its zeroth-order global L^q term. The remaining clauses of the original
claim are retained inside the negated package. The working counterexample has T=T1=1,
r=σ=β=ℓ=1, ξ=0, μ1=2, μ2=0, rate1=rate2=1, γ=2. -/
theorem theorem_3_1_counterexample (a : Data) (ha : a.Admissible) (hg : 1 < a.γ)
    (q : ℝ) (hq : 1 ≤ q) :
    ¬ ∃ v : Value,
      GlobalW a.par.T q v ∧ PDE30 a v ∧ C122 a.par.T v ∧
      (∀ z ∈ domain a.par.T, 0 < dyy v (z 0) (z 1) (z 2) ∧
        dy v (z 0) (z 1) (z 2) < 0) ∧
      (∀ t ∈ Ico (0 : ℝ) a.par.T, ∀ p ∈ Ioo (0 : ℝ) 1,
        Tendsto (fun y => dy v t y p) (𝓝[>] 0) atBot ∧
        Tendsto (fun y => dy v t y p) atTop (𝓝[<] 0)) ∧
      Growth a.par.T v := by sorry

end RetirePartialInfo.Duality.Supplement
