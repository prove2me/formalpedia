-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_same_left_amplification
-- name    : PolynomialPackingMM.IntegerRecursion.same_left_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:15.643578+00:00
-- url     : https://prove2.me/theorems/2618521a-aa13-4fee-9004-7e97d99fc3e8
-- title:
--   Lemma 3.2 — same-left amplification
-- statement:
--   Let $d,m,n,a,b,b',p,q,r\ge1$. Suppose an SL-PP packs $m$ targets, each $\mathrm{Full}_{a,b}[p,q,r]$ or $\mathrm{Mid}_{a,b}[p,q,r]$, using $n$ copies of $\mathrm{Full}_{a,b'}[p,q,r]$. Set
--
--   $$u=n^{2d},\qquad w=\left\lceil\frac{m^{2d}}{d+1}\right\rceil.$$
--
--   There are shapes $U_i\cong T^d_{a,b}$ and an SL-PP of the $w$ targets $U_i[(pq)^d,(pq)^d,r^{2d}]$ using $u$ copies of $T^d_{a,b'}[(pq)^d,(pq)^d,r^{2d}]$. The input mode, exact or modulo $\varepsilon$, is preserved. This yields balanced amplification while retaining the possibly different target variable arrangements.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
--   - encoding: w is the ceiling of m^(2d)/(d+1) → w=(m^(2d)+d)/(d+1) by natural division; reason: the denominator d+1 is positive and this is the exact integer ceiling
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 14 (PDF 15), Lemma 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem same_left_amplification :
  ∀ (mode : Mode) (d m n a b b' p q r : ℕ+)
    (choices : Fin (m : ℕ) → Bool),
  HasSLPacking mode (mixedTargets m a b p q r choices)
    (copies n (product (full a b') p q r)) →
  let u := (n : ℕ) ^ (2 * (d : ℕ))
  let w := amplifiedCount d m
  ∃ U : Fin w → Shape,
    (∀ i, (U i).Isomorphic (balanced d a b)) ∧
    HasSLPacking mode
      (List.ofFn (fun i => product (U i) ((p * q) ^ (d : ℕ))
        ((p * q) ^ (d : ℕ)) (r ^ (2 * (d : ℕ)))))
      (copies u (product (balanced d a b') ((p * q) ^ (d : ℕ))
        ((p * q) ^ (d : ℕ)) (r ^ (2 * (d : ℕ))))) := by sorry

end PolynomialPackingMM.IntegerRecursion
