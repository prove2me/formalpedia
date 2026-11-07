-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_isSymmetricRel_eq_ham
-- name    : SymBoolPCSP.CFixing.isSymmetricRel_eq_ham
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:39:33.573606+00:00
-- url     : https://prove2.me/theorems/0e11fca7-7777-43c3-863c-de0035943598
-- title:
--   A symmetric Boolean relation is the Hamming relation of its weights
-- statement:
--   Let $P \subseteq \{0,1\}^k$ be symmetric, meaning it is closed under all permutations of coordinates. Then
--
--   $$
--   P = \mathrm{Ham}_k\big(\{|x| : x \in P\}\big).
--   $$
--
--   That is, a symmetric Boolean relation is determined by its set of Hamming weights. Any two tuples of the same weight differ by a coordinate permutation. This is the identification $P_R = \mathrm{Ham}_k(S)$ used throughout §4 of Brakensiek–Guruswami.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §2.4 and §4, p. 12 (symmetric relations as Ham_k(S))

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- A symmetric Boolean relation is the Hamming relation of its set of weights: `P = Ham_k({|x| : x ∈ P})`. -/
theorem isSymmetricRel_eq_ham {k : ℕ} {P : Set (Fin k → Bool)} (hP : IsSymmetricRel P) :
    P = Ham k {s | ∃ x ∈ P, hw x = s} := by sorry

end SymBoolPCSP.CFixing
