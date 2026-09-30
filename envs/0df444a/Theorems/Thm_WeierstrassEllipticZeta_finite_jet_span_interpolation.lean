-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_jet_span_interpolation
-- name    : WeierstrassEllipticZeta.finite_jet_span_interpolation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T02:35:10.559414+00:00
-- url     : https://prove2.me/theorems/7805b456-d479-4b11-8665-4ecbbabc6daf
-- title:
--   Supported interpolation from the span of joint jet vectors
-- statement:
--   Let $K$ be a field, $R=K[\sigma]$ a polynomial ring, $D:R\to R$ a $K$-derivation, and $v_a\in K^\sigma$ an indexed family of points. Fix an integer $N\ge0$, a finite exponent set $S$, and a polynomial $p\in R$. Define the jet vector
--   $$\mathcal J(p)_{a,k}=(D^k p)(v_a),\qquad 0\le k<N.$$
--   Then
--   $$
--   \exists q\in R,\ \operatorname{supp}(q)\subseteq S\ \text{ and }\ \mathcal J(p-q)=0
--   \quad\Longleftrightarrow\quad
--   \mathcal J(p)\in\operatorname{span}_K\{\mathcal J(X^d):d\in S\}.
--   $$
--   The same polynomial $q$ serves all points and all orders. No independence or nonvanishing of the listed jet vectors is assumed. The equivalence includes $N=0$, an empty exponent set, and an empty point family. For finitely many points it is a finite linear system; the equivalence also holds for arbitrary indexed point families.
-- source:
--   Derived jet-span interpolation criterion for the frontier https://prove2.me/theorems/bd5bb8a3-3114-4e8d-883c-ee2a0555c3c9. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting equivalence uses linear jet evaluation and the monomial span of polynomials with restricted support in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric bound remains open.

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem WeierstrassEllipticZeta.finite_jet_span_interpolation
    (K σ ι : Type*) [Field K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (v : ι → σ → K) (N : ℕ) (S : Finset (σ →₀ ℕ)) (p : MvPolynomial σ K) :
    (∃ q : MvPolynomial σ K, q.support ⊆ S ∧
      ∀ a : ι, ∀ k : Fin N, MvPolynomial.eval (v a) (D^[k.val] (p - q)) = 0) ↔
    (fun (a : ι) (k : Fin N) => MvPolynomial.eval (v a) (D^[k.val] p)) ∈
      Submodule.span K
        ((fun d : σ →₀ ℕ => fun (a : ι) (k : Fin N) =>
          MvPolynomial.eval (v a) (D^[k.val] (MvPolynomial.monomial d 1))) ''
            (S : Set (σ →₀ ℕ))) := by sorry
