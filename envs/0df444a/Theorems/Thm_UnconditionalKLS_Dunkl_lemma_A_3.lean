-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_A_3
-- name    : UnconditionalKLS.Dunkl.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:12:00.712856+00:00
-- url     : https://prove2.me/theorems/2b3cbc34-46f9-47b0-852f-baabb7d3c1c2
-- title:
--   Lemma A.3 — sign and absolute-value operations in the form domain
-- statement:
--   Fix $n\ge1$, $S>0$ and $W$ satisfying (2.4). Let $f\in D(A^{1/2})$ be odd in coordinate $i$, as an $L^2(\eta)$ identity. Put $h(x)=\operatorname{sgn}(x_i)f(x)$ and $v(x)=\operatorname{sgn}(x_i)|f(x)|$. Then both functions lie in the same form domain and
--   $$\mathcal E(h)=\mathcal E(f)-\mathbb E_\eta[c_i(D_if)^2],\qquad\mathcal E(v)\le\mathcal E(f).$$
--   The subtracted integrand is integrable. The assertion is for the full form domain and does not restrict $f$ to compact support or classical differentiability. It licenses the parity and sign operations used on eigenfunctions and their derivatives.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 36, Lemma A.3; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_A_3 {n : ℕ} (hn : 0 < n) (S : ℝ) (W f : Fn n) (i : Fin n)
    (hS : 0 < S) (hW : Admissible W) (hf : FormDomain S W f)
    (hodd : (fun x => f (reflect i x)) =ᵐ[eta S W] (fun x => -f x)) :
    let h : Fn n := fun x => SignType.sign (x i) * f x
    let v : Fn n := fun x => SignType.sign (x i) * |f x|
    FormDomain S W h ∧ FormDomain S W v ∧
    Integrable (fun x => cj S i x * (difference f i x)^2) (eta S W) ∧
    energy S W h = energy S W f - (∫ x, cj S i x * (difference f i x)^2 ∂eta S W) ∧
    energy S W v ≤ energy S W f := by sorry
end UnconditionalKLS.Dunkl
