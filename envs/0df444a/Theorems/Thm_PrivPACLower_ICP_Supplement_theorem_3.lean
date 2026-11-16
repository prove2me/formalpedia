-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_3
-- name    : PrivPACLower.ICP.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:26.767516+00:00
-- url     : https://prove2.me/theorems/b9f5dd92-8911-4a27-be5b-74e8d3cd0e5d
-- title:
--   Theorem 3 — product versus union: same VC and Littlestone dimensions, different private sample complexity
-- statement:
--   There are universal constants $\varepsilon_0,\alpha_0,\beta_0\in(0,1)$, $c_0>0$ and $c,C>0$ such that for all integers $1\le v\le D$ and every admissible choice of block lengths $r_i\in\{\lfloor D/v\rfloor,\lceil D/v\rceil\}$ with $\sum_i r_i=D$, writing $\delta_{v,D}=c_0/(v+L_U)$:
--
--   1. $\mathrm{VC}(P_{v,D})=\mathrm{VC}(U_{v,D})=v$ and $\mathrm{LDim}(P_{v,D})=\mathrm{LDim}(U_{v,D})=D$;
--   2. $$c\,vL_P\ \le\ m_{\rm priv}(P_{v,D};\varepsilon_0,\delta_{v,D},\alpha_0,\beta_0)\ \le\ C\,\frac{vL_P}{\varepsilon_0\alpha_0}\log^2\frac{vL_P}{\beta_0\delta_{v,D}};$$
--   3. $$c\,(v+L_U)\ \le\ m_{\rm priv}(U_{v,D};\varepsilon_0,\delta_{v,D},\alpha_0,\beta_0)\ \le\ C\,\frac{v+L_U\log^2(L_U/(\beta_0\delta_{v,D}))+\log(1/\beta_0)}{\varepsilon_0\alpha_0}.$$
--
--   Here $L_P=\log^*(\max\{2,D/v\})$ and $L_U=\log^*(\max\{2,D\})$. The paper writes $\widetilde\Theta(vL_P)$ and $\widetilde\Theta(v+L_U)$; the lower constants are uniform and the upper bounds are those of Lemmas 20 and 24 (Appendix A) at these parameters, which are $vL_P$ and $v+L_U$ times polylogarithmic factors. The theorem shows that VC and Littlestone dimension together do not determine private sample complexity.
--
--   **Formalization Note** Logarithms in the upper bounds are natural; a change of base is absorbed in $C$.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: least sample size, possibly nonexistent → mpriv in Nat-infinity (sInf, infinity when no learner exists), coerced into ENNReal by costReal; reason: unlearnable classes have infinite cost; the inequalities are read in the extended nonnegative reals
--   - encoding: Theta-tilde(v L_P) and Theta-tilde(v + L_U) → uniform lower constant c and the upper bounds of Lemma 20 and Lemma 24 with a universal C, all quantified before v, D and the block lengths; reason: Appendix A (pp. 37–40) supplies exactly these factors at the theorem's parameters
--   - reading: the classes built from one choice of r_i in {floor(D/v), ceil(D/v)} with sum D → every admissible choice of block lengths; reason: the paper fixes an arbitrary admissible choice; the statement holds for each of them
--   - encoding: the domains X_P = union of {i} x [N_i] and A disjoint-union B; VC and Littlestone dimension → Sigma i, Fin (2^(r_i)) and Fin v + Fin (2^D - 1), x standing for x + 1; UnderstandingML.vcDim and UnderstandingML.ldim (published); reason: bijective relabelling of the finite domains; the published dimensions are the notions of p. 11
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 12, Theorem 3, with Lemmas 17, 18, 20, 24, 25 and proof pp. 36–40. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivPACLower_ICP_Supplement_Classes
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_3 :
    ∃ ε₀ α₀ β₀ c₀ : ℝ, (0 < ε₀ ∧ ε₀ < 1) ∧ (0 < α₀ ∧ α₀ < 1) ∧ (0 < β₀ ∧ β₀ < 1) ∧ 0 < c₀ ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ v D : ℕ, 1 ≤ v → v ≤ D → ∀ r : Fin v → ℕ, AdmissibleBlocks v D r →
          UnderstandingML.vcDim (ProductClass v r) = v ∧
          UnderstandingML.ldim (ProductClass v r) = D ∧
          UnderstandingML.vcDim (UnionClass v D) = v ∧
          UnderstandingML.ldim (UnionClass v D) = D ∧
          ENNReal.ofReal (c * (v * LP v D)) ≤
            costReal (mpriv (ProductClass v r) ε₀ (c₀ / (v + LU D)) α₀ β₀) ∧
          costReal (mpriv (ProductClass v r) ε₀ (c₀ / (v + LU D)) α₀ β₀) ≤
            ENNReal.ofReal (C * (v * LP v D) / (ε₀ * α₀) *
              Real.log (v * LP v D / (β₀ * (c₀ / (v + LU D)))) ^ 2) ∧
          ENNReal.ofReal (c * (v + LU D)) ≤
            costReal (mpriv (UnionClass v D) ε₀ (c₀ / (v + LU D)) α₀ β₀) ∧
          costReal (mpriv (UnionClass v D) ε₀ (c₀ / (v + LU D)) α₀ β₀) ≤
            ENNReal.ofReal (C * (v + LU D * Real.log (LU D / (β₀ * (c₀ / (v + LU D)))) ^ 2 +
              Real.log (1 / β₀)) / (ε₀ * α₀)) := by sorry

end PrivPACLower.ICP.Supplement
