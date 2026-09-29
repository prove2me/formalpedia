-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
-- name    : WeierstrassCurve.exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d289d9b0-dc33-54a7-88f1-48fec6248982
-- title:
--   Galois-equivariant injection of n-torsion into p-adic points
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime and let $n$ be a natural number. Write $W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$ and $W_{\mathbb{Q}_p}$ for its base change along $\mathbb{Z}\to\mathbb{Q}_p$, and consider the groups of affine points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ and of $W_{\mathbb{Q}_p}$ over $\overline{\mathbb{Q}_p}$, each carrying its action of the corresponding absolute Galois group by coordinatewise application of field automorphisms, together with the $n$-torsion submodules $\{P : n\cdot P = 0\}$ for the $\mathbb{Z}$-module structure. The assertion is that there exists an additive group homomorphism $\psi$ from the $n$-torsion of $W_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the $n$-torsion of $W_{\mathbb{Q}_p}(\overline{\mathbb{Q}_p})$ such that $\psi$ is injective and, for every $\mathbb{Q}_p$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}_p}$ and every $n$-torsion point $P$ over $\overline{\mathbb{Q}}$, $\psi(\mathrm{localGaloisToGlobal}\,p\,(\tau)\cdot P) = \tau\cdot\psi(P)$; here [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) is the monoid homomorphism sending $\tau$ to the restriction of $\tau$, viewed as a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}_p}$, to the normal subextension $\overline{\mathbb{Q}}$. No positivity or nondegeneracy hypothesis on $W$, $p$ or $n$ is imposed.
--
--   This is the comparison of global and local $n$-torsion along a fixed embedding $\overline{\mathbb{Q}}\hookrightarrow\overline{\mathbb{Q}_p}$: it realises the $n$-torsion of $W$ over $\overline{\mathbb{Q}}$ inside the $n$-torsion over $\overline{\mathbb{Q}_p}$ compatibly with the map from the local to the global Galois group, so that the local Galois action on $W[n]$ may be read off from the global one. It is used in the results on $n$-torsion for curves whose discriminant is divisible by $p$, in the cases $n=3$ and $n\ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ ψ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n →+
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n,
      Function.Injective ψ ∧
      ∀ (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n),
        ψ ((localGaloisToGlobal p τ) • P) = τ • ψ P := by sorry
