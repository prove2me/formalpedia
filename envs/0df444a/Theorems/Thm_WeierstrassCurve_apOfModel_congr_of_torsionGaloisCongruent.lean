-- Prove2me | Theorems.Thm_WeierstrassCurve_apOfModel_congr_of_torsionGaloisCongruent
-- name    : WeierstrassCurve.apOfModel_congr_of_torsionGaloisCongruent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/93d90a2f-4a83-5a5c-abdb-e33f9d02cc2b
-- title:
--   Congruent p-torsion gives congruent Frobenius traces
-- statement:
--   Let $p$ be a prime and let $W, W'$ be Weierstrass curves over $\mathbb{Z}$ with nonvanishing discriminants $\Delta(W) \neq 0$, $\Delta(W') \neq 0$. Write $W_{\mathbb{Q}}$, $W'_{\mathbb{Q}}$ for the curves obtained by base change along $\mathbb{Z} \to \mathbb{Q}$, and consider the groups of affine Weierstrass points over a fixed algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, each carrying the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ acting on points coordinatewise) and the $\mathbb{Z}/p$-module structure on the $p$-torsion submodule. The hypothesis is that there exists a $\mathbb{Z}/p$-linear isomorphism $\varphi$ from the $p$-torsion of $W_{\mathbb{Q}}(\overline{\mathbb{Q}})$ onto the $p$-torsion of $W'_{\mathbb{Q}}(\overline{\mathbb{Q}})$ satisfying $\varphi(\sigma \cdot x) = \sigma \cdot \varphi(x)$ for every automorphism $\sigma$ and every $p$-torsion point $x$; that is, the two mod-$p$ representations are isomorphic. Let $\ell$ be a further prime, assumed distinct from $p$, which is a good prime for both models in the sense of the project's predicate `IsGoodPrimeFor`, namely $\ell \nmid \Delta(W)$ and $\ell \nmid \Delta(W')$. The conclusion is the divisibility $p \mid W'.\mathrm{apOfModel}\ \ell - W.\mathrm{apOfModel}\ \ell$ in $\mathbb{Z}$, where for an integral model $V$ the integer $V.\mathrm{apOfModel}\ \ell$ is defined as the trace of Frobenius $\ell + 1 - \#V(\mathbb{F}_\ell)$ of the reduction of $V$ modulo $\ell$, the count being the cardinality of the set of affine Weierstrass points together with the point at infinity. Thus the traces of Frobenius of the two reductions at $\ell$ are congruent modulo $p$.
--
--   This is the standard passage from an isomorphism of mod-$p$ Galois representations attached to two elliptic curves over $\mathbb{Q}$ to the congruence $a_\ell(E') \equiv a_\ell(E) \pmod p$ at primes $\ell \neq p$ of good reduction, underlying the Eichler–Shimura style comparisons of Hecke eigenvalues. Two points of shape differ from the textbook statement: goodness at $\ell$ is the concrete condition $\ell \nmid \Delta$ for the chosen integral model rather than good reduction of a minimal model, and the hypothesis asks only for the bare existence of a $\mathbb{Z}/p$-linear Galois-equivariant isomorphism of the $p$-torsion groups, with no continuity or determinant condition; the discriminant nonvanishing hypotheses are carried along with the models. It is applied in the $3$–$5$ switch, where the auxiliary curve produced with isomorphic $5$-torsion is converted into the trace congruences modulo $5$ recorded in the statement of [`WeierstrassCurve.threeFiveSwitchCurve`](thm.html#WeierstrassCurve.threeFiveSwitchCurve).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_apOfModel_congr_of_torsionGaloisCongruent.lean

import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.apOfModel_congr_of_torsionGaloisCongruent (p : ℕ) (hp : p.Prime) (W W' : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (hφ : ∃ φ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p ≃ₗ[ZMod p] Submodule.torsionBy ℤ ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p), φ (σ • x) = σ • φ x) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓW : W.IsGoodPrimeFor ℓ) (hℓW' : W'.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p) : (p : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ) := by sorry
