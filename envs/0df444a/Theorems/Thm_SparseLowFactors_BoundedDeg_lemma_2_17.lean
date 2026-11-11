-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_17
-- name    : SparseLowFactors.BoundedDeg.lemma_2_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:23.677452+00:00
-- url     : https://prove2.me/theorems/d76a924a-9ae2-4cff-8932-85146df8ca0f
-- title:
--   Lemma 2.17 — $\dim\ker \mathrm{Syl}(f,g) = \deg\gcd(f,g)$
-- statement:
--   Let $F$ be a field and let $f,g\in F[X]$ be non-zero polynomials. Let $\mathrm{Syl}(f,g)$ be their Sylvester matrix (Definition 2.15, sizes $\deg f$ and $\deg g$). Then
--   $$\dim\ker \mathrm{Syl}(f,g)=\deg\gcd(f,g).$$
--
--   In particular the resultant vanishes exactly when $f$ and $g$ have a common factor; the lemma is the rank criterion behind the choice of a Hensel-ready point (Lemma 3.2).
--
--   **Formalization Note** The kernel is that of the linear map $F^{\deg f+\deg g}\to F^{\deg f+\deg g}$, $v\mapsto \mathrm{Syl}(f,g)v$; the gcd is the Euclidean gcd (any associate has the same degree).
--
--   Differences from the source: none.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 20, Lemma 2.17

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester

open Polynomial

namespace SparseLowFactors.BoundedDeg

open Classical in
theorem lemma_2_17 (F : Type) [Field F] (f g : Polynomial F) (hf : f ≠ 0) (hg : g ≠ 0) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (sylv f g))) = (EuclideanDomain.gcd f g).natDegree := by sorry

end SparseLowFactors.BoundedDeg
