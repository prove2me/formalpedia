-- Prove2me | Theorems.Thm_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
-- name    : TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/203c9ac8-638f-53bd-933e-96d167144187
-- title:
--   Dual numbers k[ε] as a small extension of k
-- statement:
--   Let $k$ be a field and let $k[\varepsilon] =$ `DualNumber k` $=$ `TrivSqZeroExt k k` be the algebra of dual numbers, made into a ring over $k$ via the projection `TrivSqZeroExt.fstHom`, i.e. $\varepsilon \mapsto 0$, which is used as the algebra map $k[\varepsilon] \to k$ throughout. The theorem asserts the conjunction of eight facts. First, $k[\varepsilon]$ is an Artinian ring. Second, the algebra map $k[\varepsilon] \to k$ is surjective. Third, its kernel $J$ is a nilpotent ideal. Fourth, $J \cdot \mathfrak m = \bot$, where $\mathfrak m$ is the maximal ideal of the local ring $k[\varepsilon]$. Fifth, $J \subseteq \mathfrak m$. Sixth, there exists a $k[\varepsilon]$-linear map $\iota$ from the residue field of $k[\varepsilon]$ to $k[\varepsilon]$ which is injective and whose range equals $J$, viewed as a $k[\varepsilon]$-submodule by restriction of scalars. Seventh, the composite of the structure map $k \to k[\varepsilon]$ with the residue map $k[\varepsilon] \to$ `ResidueField (DualNumber k)` is bijective. Eighth, if $k$ is algebraically closed then so is the residue field of $k[\varepsilon]$.
--
--   This is the basic small extension $k[\varepsilon] \to k$ of Schlessinger's deformation-theoretic formalism, packaged together with exactly the data (Artinian base, surjection with nilpotent kernel killed by the maximal ideal, a residue-field line inside the kernel, algebraically closed residue field) required by the re-gluing hypotheses of the bare deformation machinery. It is invoked when those hypotheses are instantiated at $B = k[\varepsilon]$, for the tangent-class package of a fake elliptic curve and for the power-series tower construction over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
    (k : Type) [Field k] :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    IsArtinianRing (DualNumber k) ∧
    Function.Surjective (algebraMap (DualNumber k) k) ∧
    IsNilpotent (RingHom.ker (algebraMap (DualNumber k) k)) ∧
    RingHom.ker (algebraMap (DualNumber k) k) * maximalIdeal (DualNumber k) = ⊥ ∧
    RingHom.ker (algebraMap (DualNumber k) k) ≤ maximalIdeal (DualNumber k) ∧
    (∃ ι : ResidueField (DualNumber k) →ₗ[DualNumber k] DualNumber k,
      Function.Injective ι ∧
      LinearMap.range ι = Submodule.restrictScalars (DualNumber k) (RingHom.ker (algebraMap (DualNumber k) k))) ∧
    Function.Bijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) ∧
    (IsAlgClosed k → IsAlgClosed (ResidueField (DualNumber k))) := by sorry
