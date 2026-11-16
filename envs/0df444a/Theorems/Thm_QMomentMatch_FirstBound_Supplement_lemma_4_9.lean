-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_4_9
-- name    : QMomentMatch.FirstBound.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:20.802641+00:00
-- url     : https://prove2.me/theorems/86dcd3a3-3348-4090-ace9-c2bc0fc06640
-- title:
--   Lemma 4.9 — $|d_\ell(\mathbf w)|\le C^\ell T^{1+\alpha_\ell}/(\sqrt\rho\,n_1 n_*^{\alpha_\ell-1/2})$ for $\sum_i w_i\le3N/4$
-- statement:
--   Setting (§4.1, p. 24). Fix integers $A\ge1$, $N\ge1$ and $T\ge0$ and a quantum algorithm $\mathcal A$ making $T$ standard queries to $f:[N]\to[N]$, with acceptance probability $p(f)=\Pr[\mathcal A^f=1]$. Let $S=\{0\}\cup[A]$, $m=\lfloor N/2\rfloor$, and for $\mathbf z\in S^m$ let $h(\mathbf z)=\mathbb E_{f\sim\mathcal D_{\mathbf c(\mathbf z)}}[p(f)]$, where $\mathbf c(\mathbf z)$ is the frequency vector of step 2 of Definition 2.1. For $\mathbf w\in S^{m-1}$ put $q_{\mathbf w}(s)=h(\mathbf w,s)$ and let $d_\ell(\mathbf w)=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom\ell s q_{\mathbf w}(s)$ be its Newton coefficients (20). Let $\alpha_\ell=1-2^{1-\ell}$.
--
--   There is an absolute constant $C>0$ with the following property. Assume (as stated before the lemma, p. 32) $N\ge8A$, $T\ge1$, $T^2\le N/8$, and fix $2\le\ell\le A$ with $T\le N^{\alpha_\ell/(1+\alpha_\ell)}$. Let $\mathbf w\in S^{m-1}$ satisfy $\sum_iw_i\le3N/4$. Complete $(\mathbf w,\ell)$ with singletons (the frequency vector $\mathbf c(\mathbf w,\ell)$ of Definition 2.1, step 2), let $\rho$ be its number of $\ell$-blocks (entries equal to $\ell$) and $b_j$ its number of $j$-blocks for $1\le j<\ell$; put $n_j=1+b_j$ and $n_*=\min_{1\le j<\ell}n_j$. Then for every $T$-query algorithm,
--   $$|d_\ell(\mathbf w)|\le\frac{C^\ell\,T^{1+\alpha_\ell}}{\sqrt\rho\;n_1\;n_*^{\alpha_\ell-1/2}}.\qquad(29)$$
--
--   Averaging (29) over random $\mathbf w$ gives Lemma 4.1.
--
--   **Formalization Note** $\sqrt\rho$ and $n_*^{\alpha_\ell-1/2}$ are real powers of natural numbers; under the hypotheses $\rho\ge1$ and $n_1,n_*\ge1$, so the denominator is positive. "$C$ is an absolute constant" is the existential $\exists C>0$ placed before every other quantity.
--
--   Differences from the source:
--   - encoding: a T-query quantum algorithm on f : [N] → [N] → QueryAlg (Fin N) (ZMod N) W T with any finite workspace W, any unitaries and start state, any output map out, standard oracle xorOracle f; reason: the base mission's algorithm model (theorem_2_5); [N] is Fin N for positions and ZMod N for labels
--   - encoding: S = {0} ∪ [A], w ∈ S^{m−1}, (w, s), m = ⌊N/2⌋ → Fin (A + 1), w : Fin (N / 2 - 1) → Fin (A + 1), appendLast w s, N / 2; reason: same conventions as the base definitions; s is placed in the last coordinate as on p. 18
--   - encoding: C is an absolute constant → ∃ C : ℝ, 0 < C placed before N, A, T, ℓ, the algorithm and w; reason: absolute means independent of every other quantity; requiring C > 0 loses nothing since enlarging to 1 + |C| preserves the bound
--   - encoding: an integer ℓ with 2 ≤ ℓ ≤ A → ℓ : Fin (A + 1) with 2 ≤ (ℓ : ℕ); reason: Fin (A + 1) carries ℓ ≤ A; ℓ is also a value of S as needed for the completion (w, ℓ)
--   - encoding: ρ, b_j counts of blocks of the completion of (w, ℓ) → Multiset.count of ℓ and j in drawsFreq N (appendLast w ℓ); reason: the completion is the base drawsFreq; a j-block is an entry equal to j
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 4.9 and the standing assumptions before it, p. 32 (setting §4.1, p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist
import Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff

namespace QMomentMatch.FirstBound.Supplement

open QAlgorithms QMomentMatch.FirstBound

/-- Lemma 4.9, p. 32, under the standing assumptions stated just before it (p. 32):
`N ≥ 8A`, `T ≥ 1`, `T² ≤ N/8`, `2 ≤ ℓ ≤ A`, `T ≤ N^{α_ℓ/(1+α_ℓ)}`. In the completion
`c(w, ℓ)`: `ρ` = number of `ℓ`-blocks, `n_1 = 1 + b_1`, `n_* = min_{1≤j<ℓ} (1 + b_j)`.
`C` is absolute. -/
theorem lemma_4_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A T : ℕ) [NeZero N] (ℓ : Fin (A + 1)),
        8 * A ≤ N → 1 ≤ T → (T : ℝ) ^ 2 ≤ (N : ℝ) / 8 → 2 ≤ (ℓ : ℕ) →
        (T : ℝ) ≤ (N : ℝ) ^ (alpha ℓ / (1 + alpha ℓ)) →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg (Fin N) (ZMod N) W T)
          (out : (Fin N × ZMod N) × W → Bool) (w : Fin (N / 2 - 1) → Fin (A + 1)),
          (∑ i, ((w i : ℕ) : ℝ)) ≤ 3 * (N : ℝ) / 4 →
          |newtonW alg out w ℓ| ≤
            C ^ (ℓ : ℕ) * (T : ℝ) ^ (1 + alpha ℓ) /
              (Real.sqrt (blockCount N w ℓ ℓ : ℝ) * ((1 + blockCount N w ℓ 1 : ℕ) : ℝ) *
                ((nStar N w ℓ : ℕ) : ℝ) ^ (alpha ℓ - 1 / 2)) := by sorry

end QMomentMatch.FirstBound.Supplement
