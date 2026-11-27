-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_19
-- name    : StochSQP.Vanishing.Supplement.lemma_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:20:14.37931+00:00
-- url     : https://prove2.me/theorems/e8e66ae6-44fc-4fff-a578-43ae8d49b968
-- title:
--   Lemma 19 (used in the proof of Theorem 1) — shifted merit decrease (corrected: lower bound of either sign)
-- statement:
--   Under the deterministic context of Appendix A, let $f_{\inf}\le f(x_k)$ for every iterate and put $\widetilde\phi(x,\tau)=\tau(f(x)-f_{\inf})+\|c(x)\|_2$. Then, for every $k$,
--   $$\widetilde\phi(x_k,\tau_k)-\widetilde\phi(x_{k+1},\tau_{k+1})\ge\eta\alpha_k\Delta l(x_k,\tau_k,g_k,d_k).$$
--   The second term uses the next merit parameter. This is the decrease statement used for the full deterministic limits.
--
--   Differences from the source:
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
--   - encoding: the infinite-run convention on p. 11 and the optional stationary stop in Appendix A → the published IsRun predicate with feasible stationary zero steps allowed; reason: finite infeasible-stationary returns already have the source certificate; extending a feasible stationary return by zero steps preserves all claimed limits, without adding a nonstationarity premise
--   - correction: (2) labels the lower objective bound f_inf positive → f_inf is any real lower bound at every iterate; reason: a constant negative objective has no positive lower bound; Assumption 1 supplies a real lower bound and the proof of Lemma 19 on p. 31 uses only f-f_inf≥0
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 31, Lemma 19; Appendix A, pp. 29–31

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic
import Definitions.Def_StochSQP_Vanishing_Supplement_ShiftedMerit

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_19
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) (fInf : ℝ) (hf : ∀ k, fInf ≤ P.f (R.x k)) : ∀ k : ℕ,
    shiftedMerit P fInf (R.x k) (R.τ k) - shiftedMerit P fInf (R.x (k+1)) (R.τ (k+1)) ≥
      A.η * R.α k * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by sorry

end StochSQP.Vanishing.Supplement
