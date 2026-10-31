-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_schurMoment
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.schurMoment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:18:26.395747+00:00
-- url     : https://prove2.me/theorems/d5e1fb25-e083-4d1e-908d-4fd5f150b659
-- title:
--   Generic moment sum equals the integral Schur expression
-- statement:
--   Let $R$ be an integral domain with $2$ invertible, $r\ge1$, and pairwise distinct $u_1,\ldots,u_r\in R$. Let $K$ be its fraction field. Define, for $a\ge0$,
--
--   $$\omega_a=\sum_{i=1}^r(2u_i-(-1)^r)u_i^a\prod_{j\ne i}\frac{u_i+u_j}{u_i-u_j}\in K.$$
--
--   Then $\omega_a=q_{a+1}(u)-(-1)^rq_a(u)/2+\delta_{a0}/2$, with the right side embedded from $R$ into $K$. In particular $\omega_a\in R$. Here the $q_a$ are defined by $\prod_i(1+u_i z)/(1-u_i z)=\sum_a q_a(u)z^a$. This identifies the constructed moment sum with a polynomial value.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 15, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 3.5, PDF p.15. The moment is computed in the fraction field;
its equality with the embedded Schur expression also gives membership in R.
The parameters are pairwise distinct, without any nonzero-sum assumption. -/
theorem schurMoment (R : Type u) [CommRing R] [IsDomain R] [Invertible (2 : R)]
    (r : ℕ) (hr : 1 ≤ r) (roots : Fin r → R)
    (hdist : ∀ i j, i ≠ j → roots i - roots j ≠ 0) (a : ℕ) :
    let emb := algebraMap R (FractionRing R)
    let moment := ∑ i : Fin r,
      (2 * emb (roots i) - (-1 : FractionRing R)^r) * emb (roots i)^a *
        ∏ j ∈ Finset.univ.erase i, (emb (roots i) + emb (roots j)) /
          (emb (roots i) - emb (roots j))
    moment = emb (evalIntegral roots (schurQ r (a+1)) -
      ⅟ (2 : R) * (-1 : R)^r * evalIntegral roots (schurQ r a) +
      if a = 0 then ⅟ (2 : R) else 0) ∧
    ∃ x : R, emb x = moment := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
