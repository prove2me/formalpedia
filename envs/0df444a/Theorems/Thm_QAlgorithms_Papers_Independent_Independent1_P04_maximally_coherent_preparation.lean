-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_maximally_coherent_preparation
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.maximally_coherent_preparation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:35.673887+00:00
-- url     : https://prove2.me/theorems/ea9b81e7-1c80-4c28-83a6-c2e8ba3c7373
-- title:
--   Preparation from the maximally coherent state
-- statement:
--   Fix $d\ge1$ and $|\Psi_d\rangle=d^{-1/2}\sum_i|i\rangle$. This is a unit vector. For each unit vector $c$, define $K_a=\sum_i c_i|i\rangle\langle i+a\bmod d|$. These matrices preserve diagonal positive operators and satisfy $\sum_a K_a^\dagger K_a=I$, with
--   $$K_a|\Psi_d\rangle\langle\Psi_d|K_a^\dagger=d^{-1}|c\rangle\langle c|.$$
--   Every density matrix $\rho$ has a finite ensemble $\rho=\sum_l p_l|c_l\rangle\langle c_l|$, with nonnegative weights summing to one and unit vectors $c_l$. The named matrices $K_{l,a}=\sqrt{p_l}\sum_i(c_l)_i|i\rangle\langle i+a\bmod d|$ form a complete incoherent Kraus family and
--   $$\sum_{l,a}K_{l,a}|\Psi_d\rangle\langle\Psi_d|K_{l,a}^\dagger=\rho.$$
--   Thus the resource prepares any target; outcomes are forgotten for mixed targets.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Eq.(4), Appendix A (A.1)–(A.6), PDF p. 5. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
















































/-- PDF pp.5–6, (A.1)–(A.6): cyclic Kraus preparation, with erasure of mixed-state outcomes. -/
theorem maximally_coherent_preparation (d : ℕ) (hd : 0 < d) :
    IsState (uniformCoherentVector d) ∧
    (∀ c : EuclideanSpace ℂ (Fin d), IsState c →
      IsKrausFamily (cyclicPureKraus c) ∧
      (∀ i, PreservesDiagonalBranch (cyclicPureKraus c i)) ∧
      ∀ i, conjSuperop (cyclicPureKraus c i) (pureDensity (uniformCoherentVector d)) =
        ((d : ℂ)⁻¹) • pureDensity c) ∧
    ∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      ∃ (a : ℕ) (p : Fin a → ℝ) (c : Fin a → EuclideanSpace ℂ (Fin d)),
        Learning.IsDistribution p ∧ (∀ i, IsState (c i)) ∧
        rho = ensembleMixture p (fun i => pureDensity (c i)) ∧
        IsKrausFamily (cyclicMixedKraus p c) ∧
        (∀ i, PreservesDiagonalBranch (cyclicMixedKraus p c i)) ∧
        krausApply (cyclicMixedKraus p c) (pureDensity (uniformCoherentVector d)) = rho := by sorry


















end QAlgorithms.Papers.Independent.Independent1.P04
