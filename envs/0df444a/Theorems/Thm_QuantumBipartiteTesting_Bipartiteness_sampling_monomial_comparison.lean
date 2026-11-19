-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_sampling_monomial_comparison
-- name    : QuantumBipartiteTesting.Bipartiteness.sampling_monomial_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:58:31.462465+00:00
-- url     : https://prove2.me/theorems/5602f9a2-bba3-49af-83a0-c4fd370caf7a
-- title:
--   Finite formal-to-feasible comparison for one response monomial
-- statement:
--   Fix valid sampling parameters $N,M,l$: there are $l\ge1$ hidden blocks, $N\le M$, and $2l$ divides $M$. Let $T$ be a canonical partial response table, with at most one non-null response at each query address, and assume that the block capacity satisfies
--
--   $$
--   4|T|\le M/l.
--   $$
--
--   For either signing law $s\in\{\mathrm{yes},\mathrm{no}\}$, write $m_T$ for the product of the response indicators prescribed by $T$. Then
--
--   $$
--   \left|\mathbb E_{\mathrm{feas},s}[m_T]-\operatorname{FormalMonomial}_s(T;M,l)\right|
--   \le\Pr[\mathrm{overflow}].
--   $$
--
--   The feasible expectation uses independent uniform block labels conditioned on no overflow, uniform compatible ambient injections, independent perfect matchings in each block and color, and the specified signing law. The formal term is the published partition-sum topology functional multiplied by its signing probability, and is zero for inconsistent tables.
--
--   This finite comparison supplies the monomial-level estimate used to pass from circuit response polynomials to the uniform formal-to-feasible acceptance error. The capacity hypothesis ensures that every placement of the observed pattern itself fits in a block, even when the full input assignment overflows.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 3.12 and Appendix A.4, monomial coupling estimate in the proof; the formal topology functional is (A.2)–(A.4) in Appendix A.2, printed pp.30–31. The explicit finite capacity condition is sufficient to realize every observed pattern placement and is eventually satisfied on the stated grid for the query regime of Lemma 3.12.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.sampling_monomial_comparison
    {N colors : ℕ} (M l : ℕ) (hValid : ValidParameters N M l)
    (T : GraphTable N colors) (hsmall : 4*T.val.card ≤ M/l) (s : Signing) :
    |FeasibleBase N M l (fun F : Finset (ColoredEdge N colors) =>
        SigningAverage s F (fun b =>
          ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az)) -
      FormalMonomial s T M l| ≤ OverflowProbability N M l := by sorry
