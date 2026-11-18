-- Prove2me | Theorems.Thm_WeldedPath_exact_query_contraction
-- name    : WeldedPath.exact_query_contraction
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T22:05:54.478997+00:00
-- url     : https://prove2.me/theorems/1a9ad409-8077-4d03-8215-b08586985851
-- title:
--   Self-adjoint contraction of exact compressed permutation queries and coherent controls
-- statement:
--   Let $s,d$ be nonnegative integers. For an arbitrary answer encoding $e:[s]\to\{0,1\}^d$, a queried point $x\in[s]$, and either the forward or inverse direction, let $\widehat O_{e,x}$ be the canonical exact compressed permutation query. Then
--   $$
--   \widehat O_{e,x}^{\dagger}=\widehat O_{e,x},\qquad \|\widehat O_{e,x}\|\le 1.
--   $$
--   The result is uniform in the encoding; injectivity of $e$ is not required. For any finite control set $C$, the encoding, queried point, and direction may depend on $c\in C$. The coherently controlled operator
--   $$
--   E=\sum_{c\in C}|c\rangle\langle c|\otimes\widehat O_{e_c,x_c}
--   $$
--   also satisfies $E^{\dagger}=E$ and $\|E\|\le1$.
--
--   This establishes the self-adjointness and contraction clauses of Lemma 2.8 for the canonical exact compressed-oracle construction, including the encoded answers used by the welded-tree oracle. The separate intertwining, database-size transition, and exact-versus-ordinary comparison clauses are outside this statement.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1, Lemma 2.8 and equations (10)-(14), with the encoded-answer convention of the canonical Supplement.exactCpOE definition and coherent-control convention of Section 2.1.

import Definitions.Def_WeldedPath_Supplement_exactCpWT

set_option autoImplicit false

namespace WeldedPath

open Classical Supplement QAlgorithms

universe u

theorem exact_query_contraction :
    ∀ s d : ℕ,
    (∀ (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool),
      ContinuousLinearMap.adjoint (exactCpOE enc x inv) = exactCpOE enc x inv ∧
      ‖exactCpOE enc x inv‖ ≤ 1) ∧
    (∀ (C : Type u) [Fintype C] [DecidableEq C]
      (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool),
      ContinuousLinearMap.adjoint (controlled (fun c => exactCpOE (enc c) (x c) (inv c))) =
        controlled (fun c => exactCpOE (enc c) (x c) (inv c)) ∧
      ‖controlled (fun c => exactCpOE (enc c) (x c) (inv c))‖ ≤ 1) := by
  sorry

end WeldedPath
