-- Prove2me | Theorems.Thm_P010_isolated_middle_path_weight
-- name    : P010.isolated_middle_path_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:00.599179+00:00
-- url     : https://prove2.me/theorems/b95b6281-0f74-4c35-8731-e47364efc97a
-- title:
--   P010: isolated middle path weight
-- statement:
--   A simple non-coprime path has either one isolated vertex or
--   at most two middle primes, never both.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L719-L737
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L719-L737

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolated_middle_path_weight (n : ℕ) (a : List ℕ)
    (hc : NonCoprimeChain a) (hd : a.Nodup)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    2 * (a.filter (fun t => decide (t ∈ isolatedVertices n))).length +
        (a.filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 2 := by sorry
