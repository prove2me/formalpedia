-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_5_3
-- name    : RSBeyondJohnson.FirstOrder.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:24.005651+00:00
-- url     : https://prove2.me/theorems/3f207568-9cea-4e07-a34e-fd6391747c1f
-- title:
--   Lemma 5.3 — rational images with a separate derivative-degree bound
-- statement:
--   Let $E$ be algebraically closed and $G\in E[Z,Y_0,Y_1]$ nonzero, of challenge degree at most $H$, total jet degree (degree in $Y_0,Y_1$) at most $j$, and $Y_1$-degree at most $r\le j$. Consider a rational map $x\mapsto(N_i(x)/\Delta(x))_i$ on a union $W$ of irreducible components of $V(G)$, whose numerators and common denominator have challenge degree at most $D_Z$, total jet degree at most $b$ and $Y_1$-degree at most $c$, where $D_Z\ge1$ and $1\le c\le b$, and assume $\Delta$ is not identically zero on any selected component. Put $D_{\mathrm{fiber}}(j,r;b,c)=jc+r(b-c)$. Then the image closure has total degree at most
--   $$H(2bc-c^2)+2D_ZD_{\mathrm{fiber}}(j,r;b,c),$$
--   and after fixing a generic challenge the image of the remaining curve components has total degree at most $D_{\mathrm{fiber}}(j,r;b,c)$.
--
--   Differences from the source:
--   - encoding: E[Z, Y₀, Y₁]; challenge, total jet and Y₁-degrees → MvPolynomial (Fin 3) E (0 = Z, 1 = Y₀, 2 = Y₁); degreeOf 0, weightedTotalDegree with weights (0, 1, 1), degreeOf 2; reason: same quantities
--   - encoding: a union of irreducible components of V(G); the denominator is nonzero on each selected component → a set of minimal primes of the vanishing ideal of V(G), W the union of their zero loci; Den ∉ 𝔭 for each selected 𝔭; reason: the components of V(G) are the zero loci of these minimal primes
--   - encoding: degree of the image closure → cdeg of the image set (cdeg of a set is that of its Zariski closure, by definition of RSCapacity_AffineGeometry); reason: total degree as on p. 25
--   - reading: after fixing a generic challenge, the image of the remaining curve components → the fiber over a challenge z* transcendental over E (in the algebraic closure of E(z*)): image of the points (z*, y₀, y₁) of the base-changed W with Δ ≠ 0; reason: 'generic' as the transcendental challenge of Lemma 4.2, where this bound is used (proof of Lemma 5.5); components over finitely many challenges miss it
--   - encoding: 2bc − c², b − c → natural subtraction; reason: nonnegative because c ≤ b
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 31–32, Lemma 5.3

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry

open MvPolynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 5.3 (Rational images with a separate derivative-degree bound)**, pp. 31–32, over an
algebraically closed field `E`. Coordinates of `E[Z, Y₀, Y₁]` are `Fin 3` (`0 = Z`, `1 = Y₀`,
`2 = Y₁`); the challenge degree is `degreeOf 0`, the total jet degree is the degree in
`(Y₀, Y₁)`, the `Y₁`-degree is `degreeOf 2`. Let `G ≠ 0` have challenge degree `≤ H`, total jet
degree `≤ j` and `Y₁`-degree `≤ r ≤ j`. Consider the rational map `x ↦ (N_i(x)/Δ(x))_i` on a union
`W` of irreducible components of `V(G)` (the zero loci of a set `comps` of minimal primes of the ideal
of `V(G)`), whose numerators `N_i` and common denominator `Δ` have challenge degree `≤ D_Z`, total
jet degree `≤ b` and `Y₁`-degree `≤ c`, with `D_Z ≥ 1`, `1 ≤ c ≤ b`, and `Δ` not identically zero on
any selected component. With `D_fiber(j, r; b, c) = jc + r(b − c)`:
(1) the image closure has total degree at most `H(2bc − c²) + 2 D_Z D_fiber(j, r; b, c)`;
(2) after fixing a generic challenge — a challenge `z*` transcendental over `E`, in the algebraic
closure `K` of `E(z*)` — the image of the remaining curve components (the points `(y₀, y₁) ∈ K²`
with `(z*, y₀, y₁)` on the base change of `W` and `Δ ≠ 0` there) has total degree at most
`D_fiber(j, r; b, c)`. -/
theorem lemma_5_3 {E : Type*} [Field E] [IsAlgClosed E] (G : MvPolynomial (Fin 3) E)
    (hG : G ≠ 0) (H j r : ℕ) (hGZ : G.degreeOf 0 ≤ H)
    (hGjet : G.weightedTotalDegree (fun i : Fin 3 => if i = 0 then 0 else 1) ≤ j)
    (hGr : G.degreeOf 2 ≤ r) (hrj : r ≤ j)
    (comps : Set (Ideal (MvPolynomial (Fin 3) E)))
    (hcomps : comps ⊆ (vanishingIdeal E (RSCapacity.zeroSet ({G} : Set (MvPolynomial (Fin 3) E)))).minimalPrimes)
    {M : ℕ} (Num : Fin M → MvPolynomial (Fin 3) E) (Den : MvPolynomial (Fin 3) E)
    (DZ b c : ℕ) (hDZ : 1 ≤ DZ) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hNum : ∀ i, (Num i).degreeOf 0 ≤ DZ ∧
      (Num i).weightedTotalDegree (fun i : Fin 3 => if i = 0 then 0 else 1) ≤ b ∧
      (Num i).degreeOf 2 ≤ c)
    (hDen : Den.degreeOf 0 ≤ DZ ∧
      Den.weightedTotalDegree (fun i : Fin 3 => if i = 0 then 0 else 1) ≤ b ∧ Den.degreeOf 2 ≤ c)
    (hDencomps : ∀ 𝔭 ∈ comps, Den ∉ 𝔭) :
    RSCapacity.cdeg {y : Fin M → E | ∃ x ∈ ⋃ 𝔭 ∈ comps, (zeroLocus E 𝔭 : Set (Fin 3 → E)),
        eval x Den ≠ 0 ∧ y = fun i => eval x (Num i) / eval x Den} ≤
      ((H * (2 * b * c - c ^ 2) + 2 * DZ * (j * c + r * (b - c)) : ℕ) : ℕ∞) ∧
    RSCapacity.cdeg {y : Fin M → AlgebraicClosure (RatFunc E) |
        ∃ y₀ y₁ : AlgebraicClosure (RatFunc E),
          (∃ 𝔭 ∈ comps, ∀ f ∈ 𝔭, eval ![algebraMap (RatFunc E) _ RatFunc.X, y₀, y₁]
            (MvPolynomial.map (algebraMap E (AlgebraicClosure (RatFunc E))) f) = 0) ∧
          eval ![algebraMap (RatFunc E) _ RatFunc.X, y₀, y₁]
            (MvPolynomial.map (algebraMap E (AlgebraicClosure (RatFunc E))) Den) ≠ 0 ∧
          y = fun i => eval ![algebraMap (RatFunc E) _ RatFunc.X, y₀, y₁]
              (MvPolynomial.map (algebraMap E (AlgebraicClosure (RatFunc E))) (Num i)) /
            eval ![algebraMap (RatFunc E) _ RatFunc.X, y₀, y₁]
              (MvPolynomial.map (algebraMap E (AlgebraicClosure (RatFunc E))) Den)} ≤
      ((j * c + r * (b - c) : ℕ) : ℕ∞) := by sorry

end RSBeyondJohnson.FirstOrder
