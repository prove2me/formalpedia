-- Prove2me | Theorems.Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic
-- name    : WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/20e1a88e-8db5-5da2-b698-2a6e4c9d21a7
-- title:
--   Bijectivity of p-torsion base change along ℚ̄→ℚ̄ₚ, singular case
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb Q$ which is not elliptic, i.e. whose discriminant fails to be a unit, let $p$ be a prime, and let $\iota \colon \overline{\mathbb Q} \to \overline{\mathbb Q_p}$ be a $\mathbb Q$-algebra homomorphism between the chosen algebraic closures of $\mathbb Q$ and of $\mathbb Q_p$. Consider the groups of affine points $(E\!\diagup\!\overline{\mathbb Q}).\mathrm{Point}$ and $(E\!\diagup\!\overline{\mathbb Q_p}).\mathrm{Point}$ of the base changes of $E$, and inside each the $\mathbb Z$-submodule $\mathrm{torsionBy}\ \mathbb Z\ \_\ p$ of points $P$ with $p \cdot P = 0$. The point map `WeierstrassCurve.Affine.Point.map ι` is an additive homomorphism, hence carries $p$-torsion to $p$-torsion (this is the side condition discharged inside the statement), and the assertion is that the induced map $$E[p](\overline{\mathbb Q}) \longrightarrow E[p](\overline{\mathbb Q_p}), \qquad P \longmapsto \iota_* P,$$ is bijective. Note that no nonsingularity of $E$ is assumed; on the contrary, the hypothesis is that $E$ is singular.
--
--   This is the singular (non-elliptic) half of the comparison of $p$-torsion over $\overline{\mathbb Q}$ and over $\overline{\mathbb Q_p}$ along an embedding of algebraic closures; it is cited by [`WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure`](thm.html#WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure), which removes the hypothesis on the discriminant and is used when comparing the global and local $p$-adic Galois representations attached to a Weierstrass curve over $\mathbb Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.bijective_torsionBy_pointMap_ratAlgClosure_padicAlgClosure_of_not_isElliptic
    (E : WeierstrassCurve ℚ) (hE : ¬ E.IsElliptic) (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p =>
        (⟨WeierstrassCurve.Affine.Point.map ι (P : (E⁄(AlgebraicClosure ℚ)).Point), by
          have hP := (Submodule.mem_torsionBy_iff _ _).mp P.property
          rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP]
          exact _root_.map_zero _⟩ :
        Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ_[p])).Point p)) := by sorry
