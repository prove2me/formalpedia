-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_3_4
-- name    : SparseLowFactors.BoundedDeg.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:38.981944+00:00
-- url     : https://prove2.me/theorems/aea74045-0ae5-4f0f-8484-7088402dc0b4
-- title:
--   Lemma 3.4 — a monic factor of a Hensel-ready monic polynomial is its factor-lift at $T=1$ (stated for any such polynomial)
-- statement:
--   Let $F$ be a field and $P\in F[X][Y]$ (in the paper, $P=\hat f_\alpha$) monic in $Y$, Hensel-ready at $X=0$, with $\mathrm{char}\,F=0$ or $>\deg_YP$. Let $L\supseteq F$ be a field over which $P(0,Y)$ splits, let $F(T,Y)=P(TX,Y)$ and $D=\deg_TF$. If $g(X,Y)$ is a factor of $P$, monic in $Y$, then $g$ is obtained from the factor-lift of $g(0,Y)$ by setting $T=1$:
--   $$g(X,Y)=\Big(\prod_{\beta\in S}(Y-\Phi_\beta(T))\ \mathrm{Trunc}\ T^{D+1}\Big)\Big|_{T=1},\qquad S=\text{roots of }g(0,Y)\text{ in }L .$$
--
--   This is the correctness core of Lemma 3.1: true factors are among the factor-lifts of the factors of $F(0,Y)$.
--
--   **Formalization Note** The factor-lift is the PowerSeriesRoots definition; $g$ is mapped to $L[X][Y]$.
--
--   Differences from the source:
--   - generalization: P = f̂_α, the shifted normalization of an s-sparse f of individual degree ≤ d (char F = 0 or > d), Hensel-ready at 0 → any P monic in Y and Hensel-ready at 0 with char F = 0 or > deg_Y P; reason: the proof uses only Corollary 2.27 and that factors of P have X-degree ≤ D; f̂_α is such a P with deg_Y ≤ d
--   - reading: "If g(X, Y) is a factor of f̂_α" → g is a factor monic in Y; reason: factors of a monic polynomial are taken monic; as printed the claim fails for g = 2, whose factor-lift is 1 (finding I1)
--   - encoding: roots of g(0, Y) → roots in a field L over which P(0, Y) splits; reason: the roots live in an extension
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 30, Lemma 3.4 (with Definition 3.3, p. 30)

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
import Definitions.Def_SparseLowFactors_BoundedDeg_PowerSeriesRoots

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem lemma_3_4 (F : Type) [Field F] (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) F))
    (hP : P.Monic) (hchar : ringChar F = 0 ∨ P.natDegree < ringChar F)
    (hHR : HenselReady P (MvPolynomial.eval 0))
    (L : Type) [Field L] [Algebra F L]
    (hsplit : ((atZero P).map (algebraMap F L)).roots.card = P.natDegree)
    (g : Polynomial (MvPolynomial (Fin n) F)) (hg : g ∣ P) (hgm : g.Monic) :
    g.map (MvPolynomial.map (algebraMap F L)) =
      (factorLift (bigF P) L (atZero g)).map (Polynomial.evalRingHom 1) := by sorry

end SparseLowFactors.BoundedDeg
