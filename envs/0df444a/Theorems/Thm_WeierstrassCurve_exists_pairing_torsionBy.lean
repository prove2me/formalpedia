-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_pairing_torsionBy
-- name    : WeierstrassCurve.exists_pairing_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/8cc59908-b35c-566c-8fd8-96a1d707b891
-- title:
--   Existence of the Weil pairing on n-torsion
-- statement:
--   Let $F$ be a field, $K$ an algebraically closed field equipped with an $F$-algebra structure, $W$ a Weierstrass curve over $F$ which is elliptic, and $n$ a natural number whose image in $K$ is nonzero. Write $E[n]$ for the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ (W⁄K).Point n` of points of the base change of $W$ to $K$ killed by $n$. The assertion is that there exists a function $e : E[n] \times E[n] \to K^{\times}$ with the following five properties: $e(P+P',Q) = e(P,Q)\,e(P',Q)$ and $e(P,Q+Q') = e(P,Q)\,e(P,Q')$ for all $P,P',Q,Q' \in E[n]$; $e(P,P) = 1$ for all $P$; for every $F$-algebra automorphism $\sigma$ of $K$ and all $P,Q$, the image of $e(\sigma\cdot P,\sigma\cdot Q)$ in $K$ equals $\sigma(e(P,Q))$, the action being the Galois action on $n$-torsion points; and nondegeneracy in the left variable, namely that $e(P,Q)=1$ for all $Q \in E[n]$ forces $P = 0$. Note that $e$ is produced as a bare function, not as a bundled bilinear or multiplicative map.
--
--   This is the existence theorem for the Weil $e_n$-pairing on the $n$-torsion of an elliptic curve, in the form used to compute determinants of the Galois representations attached to an elliptic curve; it is cited in the identification of $\det \bar\rho_{E,n}$ with the mod-$n$ cyclotomic character, in particular in the computation of the determinant of Frobenius on the Tate module and on the mod-$n$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_pairing_torsionBy.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_pairing_torsionBy {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hnK : (n : K) ≠ 0) : ∃ e : Submodule.torsionBy ℤ (W⁄K).Point n → Submodule.torsionBy ℤ (W⁄K).Point n → Kˣ, (∀ P P' Q, e (P + P') Q = e P Q * e P' Q) ∧ (∀ P Q Q', e P (Q + Q') = e P Q * e P Q') ∧ (∀ P, e P P = 1) ∧ (∀ (σ : K ≃ₐ[F] K) P Q, ((e (σ • P) (σ • Q) : Kˣ) : K) = σ (e P Q)) ∧ (∀ P, (∀ Q, e P Q = 1) → P = 0) := by sorry
