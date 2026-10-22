-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_photonThinning
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.photonThinning
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:40:27.498165+00:00
-- url     : https://prove2.me/theorems/a014b30d-8a17-43d6-947b-5ac9ba332f6c
-- title:
--   IV.A.1: photon-number thinning through random loss
-- statement:
--   Let $p_A$ be a nonnegative photon-number distribution with sum one and let $0\le t\le1$. Each of the $n$ photons independently survives with probability $t$. Summing these independent outcomes and mixing over the input photon number produces a nonnegative normalized law
--
--   $$p_B^t(k)=\sum_{m=0}^\infty p_A(m+k)\binom{m+k}{k}t^k(1-t)^m.$$
--
--   The conditional probability for $k$ survivors from $n$ photons is zero when $k>n$ and otherwise equals $\binom nk t^k(1-t)^{n-k}$. At $t=0$ the output is vacuum and at $t=1$ it is $p_A$. This is an independent-loss identity, without an assertion about arbitrary adversarial loss.
--
--   **Formalization Note** The printed factorial on page 27 is corrected to the binomial coefficient; independent moderation of this source correction remains pending.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 27, IV.A.1: photon-number thinning through random loss

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- IV.A.1, PDF p.27: independent-loss thinning. Corrects the printed reciprocal
factorial k!/[n!(n-k)!] to Nat.choose; n=2,k=1 requires 2, not 1/2.
Round-one independent moderation confirmed this minimal correction. -/
theorem photonThinning (p : PhotonLaw) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n k, survivorLaw n t k =
      if k ≤ n then (Nat.choose n k : ℝ)*t^k*(1-t)^(n-k) else 0) ∧
    (∀ k, thinned p t k = ∑' m : ℕ,
      p.mass (m+k)*(Nat.choose (m+k) k : ℝ)*t^k*(1-t)^m) ∧
    (∀ k, 0 ≤ thinned p t k) ∧ HasSum (thinned p t) 1 ∧
    thinned p 0 = vacuumLaw.mass ∧ thinned p 1 = p.mass := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
