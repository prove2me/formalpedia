-- Prove2me | Theorems.Thm_PairwiseRealize_lemma_A_1
-- name    : PairwiseRealize.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:34.958204+00:00
-- url     : https://prove2.me/theorems/56b048bc-cc0a-4515-910d-b9a27947be8c
-- title:
--   Lemma A.1, p.10 (= Lemma 2.2, p.4) — uniform geometry after deletion: the ball of radius $k/32768$ lies in the correction set
-- statement:
--   Let $\ell=\lceil\log_2(n+1)\rceil$ and $C_0=2^{44}$. Let $A,B$ be disjoint nonempty coordinate groups, $d=|A||B|$, and $|D|\le N/4096$. For $k\ge C_0(d+\ell)$ independent accepted rectangular bundles with change vectors $g_a$, and independent fair baseline bits $q^0_a$, with probability at least $1-3(n+1)^{-20}$,
--
--   $$\Bigl\{\sum_{a=1}^kg_a(p_a-q^0_a):p\in[0,1]^k\Bigr\}\supseteq\frac k{32768}B_d,$$
--
--   where $B_d$ is the Euclidean unit ball of $\mathbb R^{A\times B}$. The inclusion holds simultaneously for every vector of the ball.
--
--   The event does not depend on the residual to be corrected, so a residual may depend on the sampled reserve.
--
--   Differences from the source:
--   - generalization: Lemma 2.2: "an absolute constant C₀", k ≥ C₀(d + log n) → Lemma A.1 with C₀ = 2⁴⁴, k ≥ 2⁴⁴(d + ⌈log₂(n+1)⌉); reason: Lemma A.1 implies Lemma 2.2 with C₀ = 3·2⁴⁴, since n ≥ 2 and d ≥ 1 give d + ℓ ≤ 3(d + ln n)
--   - encoding: independent accepted bundles and fair bits → the uniform law on (accepted × Bool)^k, as a counting ratio; reason: conditioning a uniform law on acceptance gives the uniform law on accepted bundles
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Lemma A.1, p.10 (PDF p.11); Lemma 2.2, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_PairwiseRealize_Model
import Definitions.Def_PairwiseRealize_Bundles

namespace PairwiseRealize

open Classical in
/-- **Lemma A.1 (Uniform geometry after deletion), p.10 (PDF p.11); its main-text form is Lemma 2.2
(Uniform correction-ball inclusion), p.4 (PDF p.5).** K. Shi, H. Sun, *Robust Exact Realization of
Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "Put
ℓ = ⌈log₂(n + 1)⌉ and C0 = 2⁴⁴. For k ≥ C0(d + ℓ) independent accepted rectangular bundles, and
independent fair baseline bits q⁰_a, except with probability at most 3(n + 1)^{−20},
{ Σ_{a=1}^k g_a(p_a − q⁰_a) : p ∈ [0, 1]^k } ⊇ (k/32768) B_d. The inclusion holds simultaneously
for every vector in the ball." Throughout Appendix A, ε = 1/4096 and `|D| ≤ εN`.

For disjoint nonempty `A, B` with `d = |A||B|`, `|D| ≤ 2ⁿ/4096` and `k ≥ 2⁴⁴(d + ℓ)`: under the
uniform law on `k`-tuples of (accepted bundle, fair bit), the fraction of tuples for which the
Euclidean ball of radius `k/32768` in `ℝ^{A×B}` is contained in
`{Σₐ (pₐ − q⁰ₐ) gₐ : p ∈ [0, 1]^k}` is at least `1 − 3(n + 1)^{−20}`.

**Formalization Note** The accepted-bundle law is the uniform law on `acceptedBundles` (the raw law
conditioned on `E_D`), and independence of the `k` bundles and `k` bits is the product (uniform)
law on `Fin k → acceptedBundles × Bool`; the probability is a counting ratio. `B_d` is the closed
unit ball of `EuclideanSpace ℝ (A × B)`. Endpoints of different bundles may coincide. -/
theorem lemma_A_1 (n : ℕ) (A B : Finset (Fin n)) (hAB : Disjoint A B) (hA : A.Nonempty)
    (hB : B.Nonempty) (D : Finset (Row n)) (hD : 4096 * D.card ≤ 2 ^ n) (k : ℕ)
    (hk : 2 ^ 44 * (A.card * B.card + Nat.clog 2 (n + 1)) ≤ k) :
    let good : Finset (Fin k → ↥(acceptedBundles n A B D) × Bool) :=
      Finset.univ.filter fun ω =>
        Metric.closedBall (0 : EuclideanSpace ℝ (A × B)) ((k : ℝ) / 32768) ⊆
          {y | ∃ p : Fin k → ℝ, (∀ a, p a ∈ Set.Icc (0 : ℝ) 1) ∧
            y = ∑ a, (p a - bitR (ω a).2) • gvec (ω a).1.1}
    1 - 3 / ((n : ℝ) + 1) ^ 20 ≤
      (good.card : ℝ) / (Fintype.card (Fin k → ↥(acceptedBundles n A B D) × Bool) : ℝ) := by sorry

end PairwiseRealize
