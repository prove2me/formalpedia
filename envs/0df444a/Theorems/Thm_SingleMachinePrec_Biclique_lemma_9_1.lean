-- Prove2me | Theorems.Thm_SingleMachinePrec_Biclique_lemma_9_1
-- name    : SingleMachinePrec.Biclique.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:23:46.769424+00:00
-- url     : https://prove2.me/theorems/55ef7071-62b7-459a-a534-3f56e4eca7b5
-- title:
--   Lemma 9.1 — n² − an²(ln 1/a + 2) ≤ val(σ*) ≤ n² − an² for the instance S_G
-- statement:
--   Let $G=(U,V,E)$ be an $n$-by-$n$ bipartite graph and $S_G$ its bipartite scheduling instance: jobs $U\cup V$, precedence constraints $P=(U\times V)\setminus E$, the jobs of $U$ with processing time $1$ and weight $0$ and the jobs of $V$ with processing time $0$ and weight $1$. Suppose a maximum edge biclique of $G$ has value $a n^2$ for some $a\in(0,1]$. Then $S_G$ has an optimal schedule, and the value of every optimal schedule $\sigma^*$ satisfies
--
--   $$n^2-a n^2\Bigl(\ln\frac1a+2\Bigr)\;\le\;\mathrm{val}(\sigma^*)\;\le\;n^2-a n^2 ,$$
--
--   where $\ln$ is the natural logarithm.
--
--   The lemma ties the optimum of $1\,|\,\mathrm{prec}\,|\,\sum w_jC_j$ on $S_G$ to the maximum edge biclique of $G$ up to a logarithmic factor; through the hardness of maximum edge biclique it is the step from which the paper derives that $1\,|\,\mathrm{prec}\,|\,\sum w_jC_j$ has no PTAS under a complexity assumption (Theorem 9.2, not part of this statement).
--
--   **Formalization Note** The existence of an optimal schedule, implicit in the paper's "an optimal schedule $\sigma^*$", is stated as a conclusion so that the bounds are not vacuous. The paper's proof splits a sum at $(1-a)n$ and uses $\lfloor an\rfloor$; $an$ need not be an integer, and no integrality hypothesis is added.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 666, Lemma 9.1

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- Lemma 9.1 (Ambühl, Mastrolilli, Mutsanas, Svensson 2011, p. 666). Let `G = (U, V, E)` be an
`n`-by-`n` bipartite graph and `S_G` its bipartite scheduling instance (jobs `U ∪ V`, precedence
constraints `P = (U × V) \ E`, the jobs of `U` with processing time `1` and weight `0`, the jobs of
`V` with processing time `0` and weight `1`). If a maximum edge biclique of `G` has value `a n²`
for some `a ∈ (0, 1]`, then an optimal schedule `σ*` of `S_G` exists, and every optimal schedule
satisfies `n² − a n² (ln (1/a) + 2) ≤ val(σ*) ≤ n² − a n²` (natural logarithm). -/
theorem lemma_9_1 {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2) :
    (∃ l : List (U ⊕ V), IsOptimalSG E l) ∧
      ∀ l : List (U ⊕ V), IsOptimalSG E l →
        (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) ≤ valSG l ∧
          valSG l ≤ (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 := by sorry

end SingleMachinePrec.Biclique
