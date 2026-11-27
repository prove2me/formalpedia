-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_21
-- name    : StochSQP.Vanishing.Supplement.lemma_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:21:37.56449+00:00
-- url     : https://prove2.me/theorems/590c316c-e85c-40d1-a079-cdaa48dc1196
-- title:
--   Lemma 21 (used in the proof of Theorem 1) — all four positive-merit residual limits
-- statement:
--   Under the deterministic context of Appendix A, suppose $\tau_k=\tau_{\min}>0$ for all $k\ge k_\tau$. For any orthonormal basis $Z_k$ of $\operatorname{Null}(J_k)$,
--   $$\lim_{k\to\infty}\|u_k\|_2=\lim_{k\to\infty}\|d_k\|_2=\lim_{k\to\infty}\|g_k+J_k^Ty_k\|_2=\lim_{k\to\infty}\|Z_k^Tg_k\|_2=0.$$
--   Exact gradients identify the last two quantities with the Lagrangian and reduced-gradient residuals. No eventual full-rank assumption is required. This supplies all four conclusions of the printed lemma.
--
--   Differences from the source:
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
--   - encoding: the infinite-run convention on p. 11 and the optional stationary stop in Appendix A → the published IsRun predicate with feasible stationary zero steps allowed; reason: finite infeasible-stationary returns already have the source certificate; extending a feasible stationary return by zero steps preserves all claimed limits, without adding a nonstationarity premise
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 31, Lemma 21; Appendix A, pp. 29–31

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_21
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) (B : NullBases P R) (hτ : ConstantMerit R) :
    Tendsto (fun k => ‖R.u k‖) atTop (nhds 0) ∧
    Tendsto (fun k => ‖R.d k‖) atTop (nhds 0) ∧
    Tendsto (lagrangianNorm P R) atTop (nhds 0) ∧
    Tendsto (reducedNorm P R B) atTop (nhds 0) := by sorry

end StochSQP.Vanishing.Supplement
