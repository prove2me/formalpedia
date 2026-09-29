-- Prove2me | Theorems.Thm_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
-- name    : TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/e8ad25e9-d1b9-5153-96d6-82ee7900dc66
-- title:
--   Characteristic polynomial on the Tate module from kernel counts
-- statement:
--   Let $p$ be a prime, $M$ an additive commutative group and $r$ a natural number, and suppose that for every $n$ the $\mathbb{Z}$-torsion submodule of $M$ killed by $p^n$ has exactly $(p^n)^r$ elements. Let $\alpha : M \to M$ be an additive endomorphism and let $P \in \mathbb{Z}[X]$ be monic. Assume two counting hypotheses about the $\mathbb{Z}$-linear endomorphisms $G(\alpha)$ obtained by evaluating monic $G \in \mathbb{Z}[X]$ at $\alpha$: first, whenever the resultant $\operatorname{Res}(G,P)$ is nonzero, the $p$-primary component of $\ker G(\alpha)$ has cardinality $p^{e}$, where $e$ is the exponent of $p$ in the factorisation of the natural number $|\operatorname{Res}(G,P)|$; second, whenever $\operatorname{Res}(G,P) = 0$, that $p$-primary component is not finite. Let $T_p M$ be the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ for all $n$, a $\mathbb{Z}_p$-module, and let $b$ be a $\mathbb{Z}_p$-basis of $T_p M$ indexed by $\mathrm{Fin}\ r$. Then the characteristic polynomial of the matrix, in the basis $b$, of the endomorphism of $T_p M$ induced by $\alpha$ componentwise equals the image of $P$ under $\mathbb{Z} \to \mathbb{Z}_p$.
--
--   This is the algebraic mechanism, going back to Weil and presented for abelian varieties by Mumford, by which counting kernels of the endomorphisms $G(\alpha)$ pins down the characteristic polynomial of the induced endomorphism of the $p$-adic Tate module; the counting hypotheses are what the degree of an isogeny supplies in the geometric situation. It is used in the analysis of torsion on the Jacobian, through [`AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong`](thm.html#AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong), and rests on the computation of the order of the $p$-primary part of $\ker\alpha$ as $p$ to the valuation of the determinant of the induced map on $T_p M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
    (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (hker : ∀ G : Polynomial ℤ, G.Monic → G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p) =
        p ^ ((G.resultant P).natAbs.factorization p))
    (hker0 : ∀ G : Polynomial ℤ, G.Monic → G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p))
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) :
    (LinearMap.toMatrix b b (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).charpoly =
      P.map (Int.castRingHom ℤ_[p]) := by sorry
