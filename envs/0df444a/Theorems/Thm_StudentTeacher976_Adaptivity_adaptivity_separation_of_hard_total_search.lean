-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation_of_hard_total_search
-- name    : StudentTeacher976.Adaptivity.adaptivity_separation_of_hard_total_search
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:36.640136+00:00
-- url     : https://prove2.me/theorems/8ec9ed26-14a1-4bd6-b086-3250980c80c4
-- title:
--   Adaptivity separation in the hard total-search case
-- statement:
--   Fix a hierarchy level $i$ and assume $\Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}$. Suppose there is a specified total search relation $T(x,y)$ whose encoded-pair membership language lies in $\Delta_{i+1}^p$. One polynomial $b$ bounds every permitted answer by $|y|\le b(|x|)$, but no $\mathrm{FP}^{\Sigma_i^p}$ function selects a permitted answer on every input. For all source-admissible round and parallel-query functions $r,q$, show
--
--   $$
--   \mathrm{ST}^{\Sigma_i^p}[r+1,1]\not\subseteq\mathrm{ST}^{\Sigma_i^p}[r,q].
--   $$
--
--   This is the remaining case in a split according to efficient total-search selectors. The relation $T$, its totality, its verifier, its polynomial answer bound, and the absence of an efficient selector are explicit hypotheses. No fixed-presentation conversion principle is assumed. Together with the complementary selector case, this would establish the original semantic separation.
--
--   **Formalization Note.** At every fixed level $i$, the universal assertion of this case would imply
--
--   $$
--   \Sigma_{i+1}^p=\Pi_{i+1}^p\quad\Longrightarrow\quad
--   \Sigma_{i+1}^p\subseteq\Delta_{i+1}^p/\mathrm{poly}.
--   $$
--
--   The local Lean development proves the reverse operational witness/hierarchy interface with actual finite machines and all-input polynomial clocks. Under complement closure, it constructs positive validity certificates for every refutable relation, and the exact two semantic ST resource classes coincide. Combining the stated circuit hardness with the accepted efficient-selector case forces failure of efficient total-search selection and supplies the relation $T$ required here. Thus this remaining case retains a substantial unresolved complexity implication. At level zero it gives NP=coNP implying NP contained in P/poly. Neither the joint closure/hardness assumptions nor an unconditional counterexample is established. The checked implication is HierarchySemanticCollapse.hard_search_case_implies_complement_advice, with a standalone local proof in HierarchySemanticCollapseBundle.lean.
-- source:
--   Proof-case decomposition of Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, Theorem 1.4 p.7 and canonical construction §3.1 pp.19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf. The explicit total-search case assumption is introduced by this formal development and is not an additional assumption of the source theorem.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_Selectors
open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity
theorem adaptivity_separation_of_hard_total_search (i : ℕ)
    (hardness : ¬ Sigma (i+1) ⊆ DeltaPoly i)
    (T : SearchRelation)
    (hT : {s | ∃ x y,s=tup [x,y] ∧ T x y}∈Delta i)
    (htotal : ∀ x,∃ y,T x y)
    (b : Polynomial ℕ) (hbound : ∀ x y,T x y → y.length≤b.eval x.length)
    (hhard : ¬ ∃ F : Word → Word,InFP i F ∧ ∀ x,T x (F x))
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by sorry
end StudentTeacher976.Adaptivity
