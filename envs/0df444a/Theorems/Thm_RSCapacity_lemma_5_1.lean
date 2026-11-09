-- Prove2me | Theorems.Thm_RSCapacity_lemma_5_1
-- name    : RSCapacity.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:43.06321+00:00
-- url     : https://prove2.me/theorems/402c466b-7d09-40b7-a619-76a62cd8cf19
-- title:
--   Lemma 5.1 (Uniform fixed-slack parameters)
-- statement:
--   Fix $\gamma\in(0,1)$, an integer $L\ge1$, and let $r_0\in\mathbb N$ and $a>0$ stand for the constants $r_0,a_\vartheta$ of Proposition 4.7 at $\vartheta=\gamma/2$. There are an integer $r\ge\max\{1,r_0\}$, a constant $B_{\gamma,L}$ and a threshold $n_1$ such that for every $n\ge n_1$ and all integers $k,A$ with
--   $$1\le k\le(1-\gamma)n,\qquad k+\lceil\gamma n\rceil\le A\le n,$$
--   setting $\vartheta=\gamma/2$, $K=\lceil(1-\vartheta)A\rceil$ and $m=r^3$:
--   1. the hypotheses of Corollary 4.8 hold: $2\le K\le A\le n$, $r_0\le r<K$, $A/(K-1)\ge1/(1-\vartheta)$, and every $M\le Ln$ satisfies $M\le a(K-1)r^\vartheta/\log^4(er)$;
--   2. $K-k\ge\gamma n/2$ and $B=\lceil mA/(K-1)\rceil\le B_{\gamma,L}$;
--   3. for every prime $q\ge n$: $r<K\le q$, $B<q$ and $r^3A<q^2$.
--
--   The parameters $r,m$ and $B$ depend on $\gamma,L$ only, not on $n,k,A$: this is what makes the decoder's constants uniform in the rate.
--
--   Differences from the source:
--   - generalization: r_0, a_ϑ are the constants of Proposition 4.7 (Corollary 4.8) → every r_0 ∈ ℕ and every a > 0; r, B_{γ,L}, n_1 chosen after γ, L, r_0, a; reason: specializes to the paper's constants; the conclusion also records 1 ≤ r, which Proposition 4.7 assumes
--   - encoding: ⌈γn⌉ and K = ⌈(1 − ϑ)A⌉ → Nat.ceil; reason: the arguments are nonnegative
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 5.1, p.20 (PDF 22); hypotheses of Corollary 4.8, p.19 (PDF 21)

import Mathlib
import Definitions.Def_RSCapacity_InterpSpace

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 5.1 (Uniform fixed-slack parameters).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 5.1,
p.20 (PDF 22). Fix γ ∈ (0, 1) and an integer L ≥ 1. For all sufficiently large n, and every pair of
integers 1 ≤ k ≤ (1 − γ)n, k + ⌈γn⌉ ≤ A ≤ n, one can choose r = r(γ, L) and m = r³, independently
of n, k, A, so that, with ϑ := γ/2, K := ⌈(1 − ϑ)A⌉ (44), all hypotheses of Corollary 4.8 hold for
every instance with total incidence M ≤ Ln. Moreover, K − k ≥ γn/2, B = ⌈mA/(K − 1)⌉ ≤ B_{γ,L} (45)
for an effective constant B_{γ,L}. For every prime q ≥ n, after increasing the same lower threshold
for n, one also has r < K ≤ q, B < q, r³A < q².

**Formalization Note.** The hypotheses of Corollary 4.8 (p.19) are 2 ≤ K ≤ A ≤ n, r_0 ≤ r < K,
m = r³, A/(K − 1) ≥ 1/(1 − ϑ) and M ≤ a_ϑ (K − 1) r^ϑ/log⁴(er), where r_0, a_ϑ are the constants of
Proposition 4.7. Those are existential there, so this lemma is stated for every r_0 and every
a_ϑ > 0; r, B_{γ,L} and the threshold n_1 are chosen after (γ, L, r_0, a_ϑ) and before n, k, A, q.
The conclusion also records 1 ≤ r (Proposition 4.7 assumes it). -/
theorem lemma_5_1 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (L : ℕ) (hL : 1 ≤ L) (r₀ : ℕ) (a : ℝ)
    (ha : 0 < a) :
    ∃ r : ℕ, 1 ≤ r ∧ r₀ ≤ r ∧ ∃ Bγ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ k A : ℕ, 1 ≤ k →
      (k : ℝ) ≤ (1 - γ) * n → k + ⌈γ * n⌉₊ ≤ A → A ≤ n →
      (2 ≤ ⌈(1 - γ / 2) * A⌉₊ ∧ ⌈(1 - γ / 2) * A⌉₊ ≤ A ∧ A ≤ n ∧ r₀ ≤ r ∧
        r < ⌈(1 - γ / 2) * A⌉₊ ∧
        1 / (1 - γ / 2) ≤ (A : ℝ) / ((⌈(1 - γ / 2) * A⌉₊ : ℝ) - 1) ∧
        ∀ M : ℕ, M ≤ L * n →
          (M : ℝ) ≤ a * ((⌈(1 - γ / 2) * A⌉₊ : ℝ) - 1) * (r : ℝ) ^ (γ / 2) /
            Real.log (Real.exp 1 * r) ^ 4) ∧
      (γ * n / 2 ≤ (⌈(1 - γ / 2) * A⌉₊ : ℝ) - k ∧ Bdeg (r ^ 3) A ⌈(1 - γ / 2) * A⌉₊ ≤ Bγ) ∧
      ∀ q : ℕ, q.Prime → n ≤ q →
        r < ⌈(1 - γ / 2) * A⌉₊ ∧ ⌈(1 - γ / 2) * A⌉₊ ≤ q ∧
        Bdeg (r ^ 3) A ⌈(1 - γ / 2) * A⌉₊ < q ∧ r ^ 3 * A < q ^ 2 := by sorry

end RSCapacity
