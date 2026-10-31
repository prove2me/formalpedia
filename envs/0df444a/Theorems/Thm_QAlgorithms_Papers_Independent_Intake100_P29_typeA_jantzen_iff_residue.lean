-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P29_typeA_jantzen_iff_residue
-- name    : QAlgorithms.Papers.Independent.Intake100.P29.typeA_jantzen_iff_residue
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:36:12.870688+00:00
-- url     : https://prove2.me/theorems/46b9166d-1fe3-4877-8047-50e443ed9ed5
-- title:
--   Type A at q=1: Jantzen and content equivalence coincide
-- statement:
--   Let $F$ be a field of positive characteristic $p$ or characteristic zero, denoted $p=\infty$. Let $n\ge1$, $r=1$, $q=1$, and allow the unique parameter $Q_1\in F$ to be arbitrary, including zero. Let $\lambda,\mu$ be partitions of $n$. Give a node $(i,j)$ residue $j-i$ modulo $p$, with integer residues for $p=\infty$, and write $C_f$ for node counts. Jantzen coefficients are the actual signed deformation coefficients of Definition 2.5, with $X_1=Q_1t^n$ for $Q_1\ne0$ and $X_1=(t-1)t^n$ otherwise. Then
--
--   $$
--   \lambda\sim_J\mu
--   \quad\Longleftrightarrow\quad
--   \forall f\in\mathbb Z/p\mathbb Z,\ C_f(\lambda)=C_f(\mu).
--   $$
--
--   The relation $\sim_J$ uses chains of partitions of $n$. This is the type A equivalence, and does not identify all partitions as one block. In characteristic zero, the integer-content class determines the partition.
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, PDF p. 18, Corollary 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

variable {F : Type} [Field F]

/-- Corollary 4.3, PDF p. 18. Characteristic zero uses integer contents.
This is r=1,q=1 and does not assert one-block behavior for arbitrary q=1. -/
theorem typeA_jantzen_iff_residue {n : ℕ} (hn : 0 < n) (Q : Fin 1 → F)
    (L M : Multipartition 1) (hL : size L = n) (hM : size M = n) :
    JantzenEquivalent (1 : F) Q L M ↔
      ChargedResidueEquivalent (ringChar F) (fun _ => 0) L M := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P29
