-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_2_3
-- name    : UnconditionalKLS.Dunkl.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:37.995234+00:00
-- url     : https://prove2.me/theorems/303685df-c8f0-4a6e-870a-868e2b213c31
-- title:
--   Lemma 2.3 — transformed Hessian and covariance
-- statement:
--   Let $n\ge1$, $S>0$, and let $V$ be the unconditional normalized smooth potential satisfying (2.5): $0<\kappa\le K$, $\kappa I\preceq\nabla^2V\preceq KI$, and $\mathbb E_\mu X_j^2\le2$ for every coordinate, where $d\mu=e^{-V}dx$. Put $W_S=V\circ T_S$ and $\eta_S=(T_S^{-1})_\#\mu$. Then $W_S$ satisfies (2.4) and
--   $$\kappa\operatorname{diag}(q_S(|y_j|)^2)\preceq\nabla^2W_S(y)\preceq\frac{3K}{2}I,\qquad S\ge1\Longrightarrow\|\operatorname{Cov}(\eta_S)\|_{\mathrm{op}}\le14S^{2/3}.$$
--   This verifies the auxiliary model and supplies its covariance control. The statement also records the defining transport's bijectivity, its $1$-Lipschitz property, equality with the normalized weighted law, and $(T_S)_\#\eta_S=\mu$, as established in §2.1. Approximate measures need not be isotropic.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: the transport and source law fixed in (2.1)–(2.3) → bijectivity, Lipschitz bound and the two measure identities explicitly included as conclusions; reason: their properties are established from the specified map, never assumed of an arbitrary transport
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 10, Lemma 2.3; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_2_3 {n : ℕ} (hn : 0 < n) (V : Fn n) (κ K S : ℝ)
    (hV : Regular V κ K) (hS : 0 < S) :
    let W := V ∘ transport S
    Admissible W ∧
    (∀ y u, κ * (∑ j, (q S |y j|)^2 * (u j)^2) ≤ hess W y u u ∧
      hess W y u u ≤ (3*K/2) * ‖u‖^2) ∧
    (1 ≤ S → covNorm (sourceLaw S (densityLaw V)) ≤ 14 * Real.rpow S (2/3 : ℝ)) ∧
    Function.Bijective (transport S : Space n → Space n) ∧
    LipschitzWith 1 (transport S : Space n → Space n) ∧
    sourceLaw S (densityLaw V) = eta S W ∧
    Measure.map (transport S) (sourceLaw S (densityLaw V)) = densityLaw V := by sorry
end UnconditionalKLS.Dunkl
