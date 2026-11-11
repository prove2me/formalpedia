-- Prove2me | Theorems.Thm_PelagicFF_lemma_3_3
-- name    : PelagicFF.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:43.396834+00:00
-- url     : https://prove2.me/theorems/8467d9d1-7045-4a58-9d79-349e34a78e63
-- title:
--   Lemma 3.3 — coupling that stays uniform given the reveal $R$
-- statement:
--   Let $W$ be a random variable over $\{-1,1\}^N$; independently sample $I_1,\dots,I_k$ uniformly from $[N]$ with replacement; let $R=(I_1,W_{I_1},\dots,I_k,W_{I_k})$ and $I=\{I_1,\dots,I_k\}$. Then there is a coupling between $W$ and an auxiliary $U$, preserving the joint law of $(W,R)$, such that
--
--   1. for every $r$ in the support of $R$, $U\mid(R=r)\sim\mathrm{Unif}(\{-1,1\}^N)$;
--   2. $\displaystyle\mathbb E\sum_{i\notin I}(W_i-U_i)^2\le4\sqrt{N\,D_\infty(W)}$;
--   3. $\mathbb E\|W-U\|_2^2\le4\sqrt{N\,D_\infty(W)}+2k$.
--
--   It supplies the second coupling $U'$ in the proof of Lemma 4.3.
--
--   **Formalization Note** The coupling is a law on triples $(W,(I_1,\dots,I_k),U)$ whose $(W,I)$-marginal is $\mathrm{law}(W)\otimes\mathrm{Unif}([N])^{\otimes k}$; since $R=(I,W\circ I)$ this preserves the law of $(W,R)$. Conditional uniformity is stated as $\Pr[R=r,U=u]=\Pr[R=r]\cdot2^{-N}$ for all $r,u$, which needs no division and is vacuous off the support.
--
--   Differences from the source:
--   - encoding: random variables on {−1,1}^N → laws (PMF) on ι → Bool for a finite coordinate type ι with N = card ι, bit b read as sign b; reason: relabelling coordinates and values changes no instance
--   - encoding: indices sampled from [N]; R = (I₁, W_{I₁}, …, I_k, W_{I_k}) → a nonempty finite index type ι with N = card ι; R = (I, W ∘ I) with I : Fin k → ι; reason: the same data in another arrangement; [N] is nonempty for sampling
--   - encoding: U | (R = R) ∼ Unif({−1,1}^N) for R in the support of R → π(R = r ∧ U = u) = π(R = r) / 2^N for all r, u; reason: equivalent to the conditional statement on the support, both sides vanish off it
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.3, p.20

import Mathlib
import Definitions.Def_PelagicFF_minEntropyDeficiency
import Definitions.Def_PelagicFF_sqDist

open OAI.Cotype
open Classical
open scoped ENNReal

namespace PelagicFF

/-- **Lemma 3.3.** Let `W` be a random variable over `{−1,1}^N`, sample `I₁, …, I_k` independently
and uniformly from `[N]` with replacement, and let `R = (I₁, W_{I₁}, …, I_k, W_{I_k})`,
`I = {I₁, …, I_k}`. Then there is a coupling between `W` and an auxiliary `U` preserving the joint law
of `(W, R)` such that, for every `R` in the support of `R`, `U | (R = R) ∼ Unif({−1,1}^N)`, and
`E ∑_{i ∉ I} (Wᵢ − Uᵢ)² ≤ 4√(N D∞(W))`, `E‖W − U‖₂² ≤ 4√(N D∞(W)) + 2k`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.3, p.20.

**Formalization Note.** `[N]` is a nonempty finite type `ι` with `N = card ι`. The coupling is a law
`π` on triples `(W, (I₁,…,I_k), U)`. Its `(W, I)` marginal is `μ ⊗ Unif(ι)^{⊗k}`, which preserves the
joint law of `(W, R)` since `R = (I, W ∘ I)`. The conditional uniformity is stated without division:
`π(R = r, U = u) = π(R = r) · 2^{−N}` for every `r` and `u` (both sides vanish off the support). -/
theorem lemma_3_3 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (μ : PMF (ι → Bool))
    (k : ℕ) :
    ∃ π : PMF ((ι → Bool) × (Fin k → ι) × (ι → Bool)),
      (∀ (w : ι → Bool) (I : Fin k → ι),
        π.map (fun t => (t.1, t.2.1)) (w, I) = μ w * ((Fintype.card ι : ℝ≥0∞)⁻¹) ^ k) ∧
      (∀ (r : (Fin k → ι) × (Fin k → Bool)) (u : ι → Bool),
        ∑ t ∈ Finset.univ.filter
            (fun t : (ι → Bool) × (Fin k → ι) × (ι → Bool) =>
              (t.2.1, fun j => t.1 (t.2.1 j)) = r ∧ t.2.2 = u), (π t).toReal =
          (∑ t ∈ Finset.univ.filter
            (fun t : (ι → Bool) × (Fin k → ι) × (ι → Bool) =>
              (t.2.1, fun j => t.1 (t.2.1 j)) = r), (π t).toReal) / 2 ^ Fintype.card ι) ∧
      ∑ t, (π t).toReal * ∑ i ∈ Finset.univ.filter (fun i => ∀ j, t.2.1 j ≠ i),
          (sign (t.1 i) - sign (t.2.2 i)) ^ 2 ≤
        4 * Real.sqrt (Fintype.card ι * minEntropyDeficiency μ) ∧
      ∑ t, (π t).toReal * sqDist t.1 t.2.2 ≤
        4 * Real.sqrt (Fintype.card ι * minEntropyDeficiency μ) + 2 * k := by sorry

end PelagicFF
