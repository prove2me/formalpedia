-- Prove2me | Theorems.Thm_RSBDDHard_lemma_3_3
-- name    : RSBDDHard.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:34.737943+00:00
-- url     : https://prove2.me/theorems/c5643bf2-96ba-4ad0-ace8-59976034ec81
-- title:
--   Lemma 3.3 — products of complete orbits modulo $Z^{p+1}$ and $Z^{d+1}$
-- statement:
--   Let $p\ge5$ be prime and $F$ a field of characteristic $p$. Let $\lambda_1,\dots,\lambda_w\in F$ with $w\ge0$, let $\Lambda=\sum_i\lambda_i$, and set
--   $$P(Z)=\prod_{i=1}^w\prod_{a\in\mathbb F_p}\bigl(1-(\lambda_i+a)Z\bigr).$$
--   Then
--
--   1. $P(Z)\equiv1-wZ^{p-1}-\mathcal L(\Lambda)Z^p\pmod{Z^{p+1}}$;
--   2. if $w\ge1$ and $d<2p$, then $P(Z)\equiv(1-Z^{p-1})^w-\mathcal L(\Lambda)Z^p(1-Z^{p-1})^{w-1}\pmod{Z^{d+1}}$.
--
--   The lemma computes the targets $G^*$ of the reduction and is used in both completeness and soundness of Theorem 1.6.
--
--   Differences from the source:
--   - generalization: F the field of the reduction, and d the depth of (1) with d/2 < p < d → any field of characteristic p, and any natural number d < 2p; reason: the lemma's own hypotheses are p ≥ 5, w ≥ 1 and d < 2p; the reduction's F and d are instances
--   - encoding: p ≥ 5 from the §3 standing assumption (1), p.18 → explicit hypothesis 5 ≤ p; reason: part 1 is false at p = 2 (F = F_2, w = 2, λ = 0), so the standing assumption is a hypothesis of the lemma
--   - encoding: congruence mod Z^r → divisibility of the difference by X^r in F[X]; reason: both sides are polynomials
-- source:
--   Gandikota, Grigorescu, Venkitesh, NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings, STOC 2027 submission (sha256 0372e933…), Lemma 3.3, pp.20–21; standing assumption (1), p.18

import Mathlib
import Definitions.Def_RSBDDHard_recipProd

set_option autoImplicit false

namespace RSBDDHard

open Polynomial

/-- **Lemma 3.3.** Gandikota, Grigorescu, Venkitesh, *NP-Hardness of Bounded Distance Decoding
for Reed-Solomon Codes and Variants, via Non-Archimedean Rings*, STOC 2027 submission (sha256
0372e933…), pp.20–21. Let `λ_1, …, λ_w ∈ F` (`w ≥ 0`), `Λ = Σ_i λ_i`, and
`P(Z) = Π_{i=1}^w Π_{a ∈ F_p} (1 − (λ_i + a)Z)`. Then

1. `P(Z) ≡ 1 − wZ^{p−1} − L(Λ)Z^p (mod Z^{p+1})`;
2. if `w ≥ 1` and `d < 2p`, then
   `P(Z) ≡ (1 − Z^{p−1})^w − L(Λ)Z^p(1 − Z^{p−1})^{w−1} (mod Z^{d+1})`.

**Formalization Note.** `p ≥ 5` is the §3 standing assumption (1) (p.18); part 1 is false at
`p = 2`. `F` is any field of characteristic `p` (an `F_p`-algebra). Congruence mod `Z^r` is
divisibility of the difference by `X^r` in `F[X]`. -/
theorem lemma_3_3 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) {F : Type*} [Field F]
    [Algebra (ZMod p) F] (w : ℕ) (l : Fin w → F) :
    (X ^ (p + 1) ∣ (∏ i, ∏ a : ZMod p, (1 - C (l i + algebraMap (ZMod p) F a) * X)) -
      (1 - (w : F[X]) * X ^ (p - 1) - C (artinSchreier p (∑ i, l i)) * X ^ p)) ∧
    (∀ d : ℕ, 1 ≤ w → d < 2 * p →
      X ^ (d + 1) ∣ (∏ i, ∏ a : ZMod p, (1 - C (l i + algebraMap (ZMod p) F a) * X)) -
        ((1 - X ^ (p - 1)) ^ w -
          C (artinSchreier p (∑ i, l i)) * X ^ p * (1 - X ^ (p - 1)) ^ (w - 1))) := by sorry

end RSBDDHard
