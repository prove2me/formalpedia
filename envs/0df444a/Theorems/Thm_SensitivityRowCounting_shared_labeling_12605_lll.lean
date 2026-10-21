-- Prove2me | Theorems.Thm_SensitivityRowCounting_shared_labeling_12605_lll
-- name    : SensitivityRowCounting.shared_labeling_12605_lll
-- status  : Open
-- author  : @yousofy
-- created : 2026-10-20T15:30:31.460456+00:00
-- url     : https://prove2.me/theorems/d0e20611-5b0f-49c8-92b4-565741c1c000
-- title:
--   Sharper simultaneous defect bounds retaining the zero-defect threshold
-- statement:
--   Every loopless tournament on 12605 vertices admits one binary edge labeling such that, simultaneously for q=0,1,2,3,4, any vertex subset I and target-color assignment for which each source row has at most q outgoing internal label mismatches has cardinality less than [23,31,38,44,50]_q. This preserves the 23-vertex zero-defect threshold while lowering the higher-tolerance thresholds. Values on non-arcs are unused. This is a finite labeling theorem, not by itself an improved separation exponent.
-- source:
--   Original note for yousofy with Codex, 20 October 2026, 'A sharper shared-labeling theorem using row counts and the asymmetric local lemma', sections Row count through Exact certificates. Independently audited mathematical proof; Lean proof unfinished. For cutoff t_q, set E_q=choose(t_q,2), a=floor((t_q−1)/2), b=E_q−t_q*a, B_q=F_q(a)^(t_q−b)*F_q(a+1)^b, p_q=2^(t_q−E_q)*B_q. Use activities x_q=p_q*(254/253)^E_q. Exact rational arithmetic gives sum_q choose(12603,t_q−2)*x_q < 1/254. Events depend only on labels of internal arcs; events with disjoint internal arc sets are jointly independent. Cover the neighbors of an event by its E_q internal arcs. For each arc, the sum of neighboring activities is at most S<1/254, so the product of (1−x) over this group exceeds 253/254. Multiplying over arcs gives the asymmetric local-lemma hypothesis. This proves existence of a labeling avoiding every bad cutoff-sized set; restriction rules out larger bad sets. The underlying finite asymmetric LLL is classical: Moser and Tardos, arXiv:0903.0544v3, Theorem 1.1, https://arxiv.org/abs/0903.0544. Exact certificate code: row_labeling_certificate.py, lll_verify(12605,[23,31,38,44,50],Fraction(254,253)). The accompanying full proof records all independence and counting obligations. Retains the accepted tournament foundation attribution https://prove2.me/theorems/49fdd176-c319-4f1e-b15f-b1fd5130f0bc.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
open scoped Classical

namespace SensitivityRowCounting
theorem shared_labeling_12605_lll
    (A : Fin 12605 → Fin 12605 → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin 12605 → Fin 12605 → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin 12605),
      ∀ colors : Fin 12605 → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < (![23,31,38,44,50] q) := by sorry
end SensitivityRowCounting
