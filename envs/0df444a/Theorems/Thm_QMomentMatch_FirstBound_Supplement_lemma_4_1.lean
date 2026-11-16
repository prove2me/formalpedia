-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_4_1
-- name    : QMomentMatch.FirstBound.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:06.390815+00:00
-- url     : https://prove2.me/theorems/53489939-fde3-4639-95fd-2938b1ac2ab4
-- title:
--   Lemma 4.1 — averaged bound $\mathbb E_{\pi^{\otimes(m-1)}}[\mathbf 1_{\mathcal G}|d_\ell|]\le\frac{C^\ell T^{1+\alpha_\ell}}{N}(ma)^{-\alpha_\ell}$ and $\Pr[\mathcal G^c]\le e^{-N/(4A^2)}$
-- statement:
--   Setting (§4.1, p. 24). Fix integers $A\ge1$, $N\ge1$ and $T\ge0$ and a quantum algorithm $\mathcal A$ making $T$ standard queries to $f:[N]\to[N]$, with acceptance probability $p(f)=\Pr[\mathcal A^f=1]$. Let $S=\{0\}\cup[A]$, $m=\lfloor N/2\rfloor$, and for $\mathbf z\in S^m$ let $h(\mathbf z)=\mathbb E_{f\sim\mathcal D_{\mathbf c(\mathbf z)}}[p(f)]$, where $\mathbf c(\mathbf z)$ is the frequency vector of step 2 of Definition 2.1. For $\mathbf w\in S^{m-1}$ put $q_{\mathbf w}(s)=h(\mathbf w,s)$ and let $d_\ell(\mathbf w)=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom\ell s q_{\mathbf w}(s)$ be its Newton coefficients (20). Let $\alpha_\ell=1-2^{1-\ell}$. Let $\mathcal G=\{\mathbf w\in S^{m-1}:\sum_iw_i\le3N/4\}$.
--
--   There is an absolute constant $C>0$ with the following property. Assume $N\ge8A$, $T\ge1$ and $T^2\le N/8$, and let $2\le\ell\le A$ satisfy $T\le N^{\alpha_\ell/(1+\alpha_\ell)}$. Let $\pi$ be a mean-one distribution on $S$ (a probability distribution with $\sum_s s\,\pi(s)=1$) with $\pi(s)\ge a>0$ for every $s\in S$. Then for every $T$-query algorithm,
--   $$\mathbb E_{\mathbf w\sim\pi^{\otimes(m-1)}}\big[\mathbf 1_{\mathcal G}(\mathbf w)\,|d_\ell(\mathbf w)|\big]\le\frac{C^\ell\,T^{1+\alpha_\ell}}{N}\,(ma)^{-\alpha_\ell},$$
--   and
--   $$\Pr_{\mathbf w\sim\pi^{\otimes(m-1)}}[\mathbf w\notin\mathcal G]\le e^{-N/(4A^2)}.$$
--
--   The proof of Theorem 2.6 applies this along linear paths of distributions to bound the residual term of the comparison Lemma 3.8.
--
--   **Formalization Note** The expectation and probability are finite sums over $S^{m-1}$ weighted by $\prod_i\pi(w_i)$ (base `prodExp`); $(ma)^{-\alpha_\ell}$ and $T^{1+\alpha_\ell}$ are real powers. The probability bound does not involve the algorithm and is stated outside the quantifier over algorithms.
--
--   Differences from the source:
--   - encoding: a T-query quantum algorithm on f : [N] → [N] → QueryAlg (Fin N) (ZMod N) W T with any finite workspace W, any unitaries and start state, any output map out, standard oracle xorOracle f; reason: the base mission's algorithm model (theorem_2_5); [N] is Fin N for positions and ZMod N for labels
--   - encoding: S = {0} ∪ [A], w ∈ S^{m−1}, (w, s), m = ⌊N/2⌋ → Fin (A + 1), w : Fin (N / 2 - 1) → Fin (A + 1), appendLast w s, N / 2; reason: same conventions as the base definitions; s is placed in the last coordinate as on p. 18
--   - encoding: C is an absolute constant → ∃ C : ℝ, 0 < C placed before N, A, T, ℓ, the algorithm and w; reason: absolute means independent of every other quantity; requiring C > 0 loses nothing since enlarging to 1 + |C| preserves the bound
--   - encoding: an integer ℓ with 2 ≤ ℓ ≤ A → ℓ : Fin (A + 1) with 2 ≤ (ℓ : ℕ); reason: Fin (A + 1) carries ℓ ≤ A; ℓ is also a value of S as needed for the completion (w, ℓ)
--   - encoding: π a mean-one distribution on S → IsProbVec π ∧ moment π 1 = 1; reason: base definitions of a law on S and its first moment
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 4.1, p. 24 (proof p. 32; setting §4.1, p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist
import Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff

namespace QMomentMatch.FirstBound.Supplement

open QAlgorithms QMomentMatch.FirstBound

/-- Lemma 4.1, p. 24 (proof p. 32), in the setting of §4.1: `m = ⌊N/2⌋`,
`G = {w ∈ S^{m−1} : ∑ w_i ≤ 3N/4}`, `w ∼ π^{⊗(m−1)}`. `C` is absolute. -/
theorem lemma_4_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A T : ℕ) [NeZero N] (ℓ : Fin (A + 1)),
        8 * A ≤ N → 1 ≤ T → (T : ℝ) ^ 2 ≤ (N : ℝ) / 8 → 2 ≤ (ℓ : ℕ) →
        (T : ℝ) ≤ (N : ℝ) ^ (alpha ℓ / (1 + alpha ℓ)) →
        ∀ (π : Fin (A + 1) → ℝ), IsProbVec π → moment π 1 = 1 →
        ∀ a : ℝ, 0 < a → (∀ s, a ≤ π s) →
          (∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg (Fin N) (ZMod N) W T)
            (out : (Fin N × ZMod N) × W → Bool),
            prodExp π (fun w : Fin (N / 2 - 1) → Fin (A + 1) =>
                goodInd N w * |newtonW alg out w ℓ|) ≤
              C ^ (ℓ : ℕ) * (T : ℝ) ^ (1 + alpha ℓ) / N *
                (((N / 2 : ℕ) : ℝ) * a) ^ (-alpha ℓ)) ∧
          prodExp π (fun w : Fin (N / 2 - 1) → Fin (A + 1) => 1 - goodInd N w) ≤
            Real.exp (-((N : ℝ) / (4 * (A : ℝ) ^ 2))) := by sorry

end QMomentMatch.FirstBound.Supplement
