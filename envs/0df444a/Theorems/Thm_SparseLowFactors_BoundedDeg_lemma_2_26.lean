-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_26
-- name    : SparseLowFactors.BoundedDeg.lemma_2_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:36.498955+00:00
-- url     : https://prove2.me/theorems/90dd049b-8b24-4964-b60b-bc56d7a0cabc
-- title:
--   Lemma 2.26 (Hensel's lemma) — a Hensel-ready monic $f$ splits into power-series roots $\Phi_i$ with $\Phi_i(0)=\beta_i$
-- statement:
--   Let $f(X,Y)\in F[X][Y]$ be monic in $Y$ with $\deg_Yf=d$, with irreducible factorization $f=h_1^{e_1}\cdots h_r^{e_r}$, and Hensel-ready at $X=0$. Let $B=\{\beta_1,\dots,\beta_d\}$ be the multiset of roots of $f(0,Y)$ in a field $L\supseteq F$ over which $f(0,Y)$ splits. Then
--   $$f(X,Y)=\prod_{i=1}^d\big(Y-\Phi_i(X)\big)$$
--   with $\Phi_i\in F(\beta_i)[[X]]$, $\Phi_i(0)=\beta_i$, and $\Phi_i=\Phi_j$ if and only if $\beta_i=\beta_j$.
--
--   Every univariate root of $f(0,Y)$ thus lifts to a unique power-series root, which is what the factoring algorithm truncates.
--
--   **Formalization Note** $B$ is given as an enumeration $\beta:\{1..d\}\to L$ of the root multiset; the identity holds in $L[[X]][Y]$, and "$\Phi_i\in F(\beta_i)[[X]]$" says every coefficient of $\Phi_i$ lies in the subfield $F(\beta_i)\subseteq L$.
--
--   Differences from the source:
--   - encoding: "B is the multiset of roots of f(0, Y)" (over a field extension) → any field L ⊇ F and any enumeration β of the root multiset of f(0, Y) in L, required to have d elements (so f(0, Y) splits in L); reason: the roots live in an extension; the statement holds in each such L
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 23, Lemma 2.26

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
import Definitions.Def_SparseLowFactors_BoundedDeg_PowerSeriesRoots

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem lemma_2_26 (F : Type) [Field F] (n d : ℕ) (f : Polynomial (MvPolynomial (Fin n) F))
    (hmon : f.Monic) (hd : f.natDegree = d) (hHR : HenselReady f (MvPolynomial.eval 0))
    (L : Type) [Field L] [Algebra F L] (β : Fin d → L)
    (hB : Multiset.map β Finset.univ.val = ((atZero f).map (algebraMap F L)).roots) :
    ∃ Φ : Fin d → MvPowerSeries (Fin n) L,
      f.map (toPS (L := L)) = ∏ i, (X - C (Φ i)) ∧
      (∀ i, ∀ m : Fin n →₀ ℕ, MvPowerSeries.coeff m (Φ i) ∈ IntermediateField.adjoin F {β i}) ∧
      (∀ i, MvPowerSeries.constantCoeff (Φ i) = β i) ∧
      ∀ i j, Φ i = Φ j ↔ β i = β j := by sorry

end SparseLowFactors.BoundedDeg
