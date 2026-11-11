-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_corollary_2_27
-- name    : SparseLowFactors.BoundedDeg.corollary_2_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:39.815813+00:00
-- url     : https://prove2.me/theorems/f7f05836-8e69-430a-9ae8-225f5b79986b
-- title:
--   Corollary 2.27 — a monic factor of $f$ is $\prod_{\beta\in S}(Y-\Phi_\beta)$ with $\mathrm{Esym}_j(S)\in F$
-- statement:
--   Let $f(X,Y)\in F[X][Y]$ be monic with $\deg_Yf=d$ and Hensel-ready at $X=0$, and let $B$ be the multiset of roots of $f(0,Y)$ in a field $L\supseteq F$ over which it splits. Let $g\in F[X][Y]$ be monic in $Y$ with $\deg_Yg=k$ and $g\mid f$. Then there is a sub-multiset $S\subseteq B$ with $|S|=k$ such that
--   $$g=\prod_{\beta\in S}(Y-\Phi_\beta)\qquad\text{and}\qquad \mathrm{Esym}_j(S)\in F\ \text{ for all } j\in[k],$$
--   where $\Phi_\beta$ is the power-series root of $f$ with constant term $\beta$.
--
--   Every monic factor of $f$ is therefore determined by a factor of $f(0,Y)$ over $F$, which is what makes the number of candidates at most $2^d-1$.
--
--   **Formalization Note** $\Phi_\beta$ is the PowerSeriesRoots definition (unique under the hypotheses, by Lemma 2.26); the identity is in $L[[X]][Y]$.
--
--   Differences from the source: none.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 23, Corollary 2.27

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
import Definitions.Def_SparseLowFactors_BoundedDeg_PowerSeriesRoots

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem corollary_2_27 (F : Type) [Field F] (n d k : ℕ) (f g : Polynomial (MvPolynomial (Fin n) F))
    (hmon : f.Monic) (hd : f.natDegree = d) (hHR : HenselReady f (MvPolynomial.eval 0))
    (L : Type) [Field L] [Algebra F L]
    (hsplit : ((atZero f).map (algebraMap F L)).roots.card = d)
    (hg : g.Monic) (hk : g.natDegree = k) (hdiv : g ∣ f) :
    ∃ S : Multiset L, S ≤ ((atZero f).map (algebraMap F L)).roots ∧ S.card = k ∧
      g.map (toPS (L := L)) = (S.map fun β => X - C (psRoot f L β)).prod ∧
      ∀ j ∈ Finset.Icc 1 k, esym j S ∈ Set.range (algebraMap F L) := by sorry

end SparseLowFactors.BoundedDeg
